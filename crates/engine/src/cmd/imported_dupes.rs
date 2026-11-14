// SPDX-FileCopyrightText: MailCraft contributors
// SPDX-License-Identifier: MIT OR Apache-2.0
//! Mail brought in twice (#1401): what makes two messages the same mail, so that an import skips
//! a message the mailbox already holds anywhere, and the clean-up that removes the copies an import
//! made, before imports did that, beside the mail a server has.
//!
//! **The same mail.** The same Message-ID, and the same date, sender, subject and To/Cc people
//! ([`MailIdentity`], the identity a renumbered IMAP mailbox's changes are matched by). A message
//! with no Message-ID, or no date, is never the same as another: the sender's other fields alone
//! could make two different messages one (a notification sent twice in a second), and an import
//! would leave one out, so such a message is always imported, and never removed as a copy.
//!
//! **The clean-up.** `mail.removeImportedDuplicates` removes a message that only this computer has
//! when the same folder holds the same mail as its server has it. It never touches the server's
//! copy, and tells the server nothing. Only a message that nothing waits on is a copy to remove: a
//! draft, a message in an Outbox or being sent, one being moved into or out of an account
//! ([`Pending::Move`], [`Queued`]), one waiting for its server's copy to be matched (`synced` with
//! no UID), and one that is the server's under any kind of id (an IMAP UID, the id a Microsoft,
//! JMAP or Exchange server gave it) are left as they are.

use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use mailcraft_model::{FolderKind, Id, MailIdentity, Mailbox, Message, Pending, Queued};
use serde_json::{Value, json};

use super::fail;
use crate::{CmdResult, CommandSpec, Session, p};

/// Most messages one clean-up names in its answer; the rest are counted.
pub const MAX_LISTED: usize = 500;

pub fn specs() -> Vec<CommandSpec> {
    vec![CommandSpec::new("mail.removeImportedDuplicates", "Remove Imported Duplicates", "Folder › Clean Up", remove).params(PARAMS)]
}

const PARAMS: &str = r#"{"folder"?: number (one folder; default every folder), "preview"?: bool (only count, change nothing)} — removes messages that only this computer has (imported from a file, nothing waiting to go to a server) when the same folder holds the same mail from its server (same Message-ID, date, sender, subject and To/Cc). The server's copy is never touched and the server is told nothing; undo puts them back → {"removed": number, "ids": [number] (at most 500), "preview": bool}"#;

/// What makes a message the same mail as another: its Message-ID, and a digest of the rest of its
/// [`MailIdentity`] (so that a folder of many thousands is held in little memory).
pub type Key = (String, u64);

/// What makes `m` the same mail as another ([`Key`]); `None` for a message with no Message-ID or
/// no date, which is never taken for another.
pub fn identity(m: &Message) -> Option<Key> {
    if m.message_id.is_empty() || m.date == 0 {
        return None;
    }
    let MailIdentity { date, from, subject, people } = MailIdentity::of(m);
    let mut h = std::collections::hash_map::DefaultHasher::new();
    (date, from, subject, people).hash(&mut h);
    Some((m.message_id.clone(), h.finish()))
}

/// What every message of the mailbox is ([`identity`]), wherever it is: what an import leaves
/// out. Built in one pass; at most one entry a message, so it is no larger than the mailbox.
pub fn index(mb: &Mailbox) -> HashSet<Key> {
    mb.messages.values().filter_map(|m| identity(m)).collect()
}

/// Whether the server has `m` under an id of its own: an IMAP UID, or the id a Microsoft, JMAP
/// or Exchange server gave it (and hasn't said is gone).
fn on_server(m: &Message) -> bool {
    m.uid != 0 || m.server.as_ref().is_some_and(|s| !s.gone && !s.id.is_empty())
}

/// Whether `m` is only this computer's and nothing waits on it: no id of a server's, no copy on
/// a server waiting to be matched to it, nothing to be sent or made of it, not a draft.
fn only_here(m: &Message) -> bool {
    m.uid == 0
        && m.server.is_none()
        && m.synced.is_none()
        && m.placed.is_empty()
        && m.moving_out.is_none()
        && m.server_draft.is_none()
        && m.answers.is_none()
        && !m.draft
        && !m.sending
        && !m.sent_here
        && m.held.is_empty()
        && m.returned == 0
        && m.original_placed == 0
}

/// The messages the clean-up removes: in `folder` (or every folder), only this computer's
/// ([`only_here`]), with nothing waiting on them in any of the mailbox's queues, and the same mail
/// ([`identity`]) as a message of the same folder that its server has. Never in an Outbox or a
/// Drafts folder. Sorted by id.
pub fn twins(mb: &Mailbox, folder: Option<Id>) -> Vec<Id> {
    let in_scope = |f: Id| folder.is_none_or(|want| want == f);
    // What waits on a message, in every queue that names one.
    let mut waited: HashSet<Id> = HashSet::new();
    for p in &mb.pending {
        if let Pending::Move { message, .. } = p {
            waited.insert(*message);
        }
    }
    for q in &mb.queued {
        match q {
            Queued::PlaceMessage { message, .. } => {
                waited.insert(*message);
            }
            Queued::CopyMessage { copy, .. } => {
                waited.insert(*copy);
            }
            Queued::DeleteFolder { .. } | Queued::DeleteMessage { .. } => {}
        }
    }
    // The server's mail of each folder, by Message-ID and what it is (compared whole: what is
    // removed must be the same mail, not one whose digest happens to agree).
    let mut theirs: HashMap<(Id, &str), Vec<MailIdentity>> = HashMap::new();
    for m in mb.messages.values().filter(|m| in_scope(m.folder) && on_server(m) && identity(m).is_some()) {
        theirs.entry((m.folder, m.message_id.as_str())).or_default().push(MailIdentity::of(m));
    }
    if theirs.is_empty() {
        return Vec::new();
    }
    let kept_out = |f: Id| mb.is_send_queue(f) || mb.folder(f).is_none_or(|f| f.kind == FolderKind::Drafts);
    let twin =
        |m: &Message| identity(m).is_some() && theirs.get(&(m.folder, m.message_id.as_str())).is_some_and(|all| all.contains(&MailIdentity::of(m)));
    let mut out: Vec<Id> =
        mb.messages.values().filter(|m| only_here(m) && !waited.contains(&m.id) && twin(m) && !kept_out(m.folder)).map(|m| m.id).collect();
    out.sort_unstable();
    out
}

fn remove(s: &mut Session, v: &Value) -> CmdResult {
    p::only(v, &["folder", "preview"])?;
    let preview = p::opt_bool(v, "preview")?.unwrap_or(false);
    let folder = p::id_strict(v, "folder")?;
    if let Some(f) = folder
        && s.mailbox.folder(f).is_none()
    {
        return Err(failed!("no folder with id {id}", id = f));
    }
    let ids = twins(&s.mailbox, folder);
    if !preview {
        // Taken out without a word to any server: none of them is a server's.
        for id in &ids {
            s.mailbox.forget_message(*id).map_err(|e| fail(e.to_string()))?;
        }
        if !ids.is_empty() {
            s.sel.messages.retain(|m| !ids.contains(m));
            s.list_due();
        }
        log::info!("imported duplicates: {} removed", ids.len());
    }
    let listed: Vec<Id> = ids.iter().copied().take(MAX_LISTED).collect();
    Ok(json!({"removed": ids.len(), "ids": listed, "preview": preview}))
}
