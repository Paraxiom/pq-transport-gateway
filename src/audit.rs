//! Audit logging for security compliance.
//!
//! One JSON line per control-plane event. Each gateway run starts a
//! *segment* with a random 32-byte `log_id`, and the lines of a segment form
//! a hash chain over their exact bytes as written (without the newline):
//!
//! ```text
//! h_start = H(D[audit/v1/genesis], [log_id])
//! h_seq   = H(D[audit/v1/entry],   [h_prev, line_bytes])
//! ```
//!
//! A `checkpoint` line carries an SLH-DSA-Shake128f signature by the
//! gateway's persisted identity over
//! `H(D[audit/v1/checkpoint], [log_id, be64(through_seq), h_through_seq])`.
//! The first line of a segment (`segment_start`) records
//! `H(D[audit/v1/tail], [line])` of the line before it in the file, which
//! links the segment to whatever the file already held. [`verify_log`]
//! (`--verify-audit-log`) checks all of it. Vectors:
//! `tests/vectors/audit-v1.json`.
//!
//! What this does not cover (`docs/THREAT-MODEL.md` S4, T9): the signing key
//! is a file on the same host, so whoever controls the host can re-sign a
//! forged log; events after the last checkpoint stay unsigned until the next
//! one; and removing the end of the file, its last checkpoint included,
//! leaves nothing to detect unless checkpoints were copied elsewhere.

use crate::crypto::PqKeyExchange;
use crate::kdf::{self, AUDIT_V1_CHECKPOINT, AUDIT_V1_ENTRY, AUDIT_V1_GENESIS, AUDIT_V1_TAIL};
use anyhow::{anyhow, bail, Result};
use base64::engine::general_purpose::STANDARD as B64;
use base64::Engine as _;
use chrono::{DateTime, Utc};
use rand::RngCore;
use serde::Serialize;
use serde_json::{json, Value};
use std::fs::{File, OpenOptions};
use std::io::{BufRead, Read, Seek, SeekFrom, Write};
use std::net::SocketAddr;
use std::path::Path;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock};
use std::time::Duration;
use tokio::sync::Notify;

/// Format tag written in every `segment_start`.
pub const FORMAT: &str = "pqtg-audit-v1";

const SEGMENT_START: &str = "segment_start";
const CHECKPOINT: &str = "checkpoint";
const SIGNATURE_ALG: &str = "slh-dsa-shake128f";

static AUDIT_LOG: OnceLock<Arc<AuditLog>> = OnceLock::new();

/// Start of a segment's chain.
pub fn chain_genesis(log_id: &[u8; 32]) -> [u8; 32] {
    kdf::hash(&AUDIT_V1_GENESIS, &[log_id.as_slice()])
}

/// Chain step over one line, as written and without its newline.
pub fn chain_entry(prev: &[u8; 32], line: &[u8]) -> [u8; 32] {
    kdf::hash(&AUDIT_V1_ENTRY, &[prev.as_slice(), line])
}

/// The 32 bytes a checkpoint signs.
pub fn checkpoint_message(log_id: &[u8; 32], through_seq: u64, head: &[u8; 32]) -> [u8; 32] {
    kdf::hash(
        &AUDIT_V1_CHECKPOINT,
        &[
            log_id.as_slice(),
            &through_seq.to_be_bytes(),
            head.as_slice(),
        ],
    )
}

/// What a `segment_start` records about the line before it.
pub fn tail_hash(line: &[u8]) -> [u8; 32] {
    kdf::hash(&AUDIT_V1_TAIL, &[line])
}

#[derive(Serialize)]
struct AuditEntry<'a> {
    seq: u64,
    timestamp: DateTime<Utc>,
    event_type: &'a str,
    details: Value,
}

/// An open audit log: appends chained lines and writes checkpoints.
pub struct AuditLog {
    state: Mutex<State>,
    signer: Option<Arc<PqKeyExchange>>,
    checkpoint_every: u64,
    wake: Notify,
}

struct State {
    out: File,
    log_id: [u8; 32],
    head: [u8; 32],
    next_seq: u64,
    /// Lines other than checkpoints written in this segment.
    events: u64,
    /// `events` as of the last checkpoint written.
    events_signed: u64,
}

/// What the next checkpoint covers: taken under the lock, signed outside it.
pub struct Snapshot {
    log_id: [u8; 32],
    through_seq: u64,
    head: [u8; 32],
    events: u64,
}

impl AuditLog {
    /// Open (or create) the log at `path` and start a new segment. With a
    /// signer, checkpoints are signed by its SLH-DSA key; without one the
    /// segment is hash-chained only and marked `"signed": false`.
    pub fn open(
        path: &Path,
        signer: Option<Arc<PqKeyExchange>>,
        checkpoint_every: u64,
    ) -> Result<Arc<Self>> {
        if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
            std::fs::create_dir_all(parent)?;
        }
        let mut out = OpenOptions::new()
            .create(true)
            .read(true)
            .append(true)
            .open(path)?;
        let prev_line = last_line(&mut out)?;

        let mut log_id = [0u8; 32];
        rand::rngs::OsRng.fill_bytes(&mut log_id);
        let log = Arc::new(Self {
            state: Mutex::new(State {
                out,
                log_id,
                head: chain_genesis(&log_id),
                next_seq: 0,
                events: 0,
                events_signed: 0,
            }),
            checkpoint_every: checkpoint_every.max(1),
            wake: Notify::new(),
            signer,
        });
        let details = json!({
            "format": FORMAT,
            "log_id": hex(&log_id),
            "prev_tail": prev_line.map(|l| hex(&tail_hash(&l))),
            "signed": log.signer.is_some(),
            "slh_dsa_vk": log.signer.as_ref().map(|s| hex(s.slh_dsa_pk_bytes())),
            "version": env!("CARGO_PKG_VERSION"),
        });
        log.append(SEGMENT_START, details)?;
        Ok(log)
    }

    /// Append one event. `segment_start` and `checkpoint` are reserved.
    pub fn record(&self, event_type: &str, details: Value) -> Result<()> {
        if event_type == SEGMENT_START || event_type == CHECKPOINT {
            bail!("audit event type {event_type} is reserved");
        }
        self.append(event_type, details)
    }

    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn append(&self, event_type: &str, details: Value) -> Result<()> {
        let mut st = self.lock();
        let entry = AuditEntry {
            seq: st.next_seq,
            timestamp: Utc::now(),
            event_type,
            details,
        };
        let mut line = serde_json::to_vec(&entry)?;
        let head = chain_entry(&st.head, &line);
        line.push(b'\n');
        st.out.write_all(&line)?;
        st.out.flush()?;

        st.head = head;
        st.next_seq += 1;
        if event_type != CHECKPOINT {
            st.events += 1;
            if self.signer.is_some() && st.events - st.events_signed >= self.checkpoint_every {
                self.wake.notify_one();
            }
        }
        Ok(())
    }

    /// The checkpoint to sign next, or `None` if the log is unsigned or no
    /// event arrived since the last checkpoint (an idle gateway writes none).
    pub fn snapshot(&self) -> Option<Snapshot> {
        self.signer.as_ref()?;
        let st = self.lock();
        if st.events == st.events_signed {
            return None;
        }
        Some(Snapshot {
            log_id: st.log_id,
            through_seq: st.next_seq.checked_sub(1)?,
            head: st.head,
            events: st.events,
        })
    }

    fn write_checkpoint(&self, snap: &Snapshot, signature: &[u8]) -> Result<()> {
        self.append(
            CHECKPOINT,
            json!({
                "through_seq": snap.through_seq,
                "chain_head": hex(&snap.head),
                "alg": SIGNATURE_ALG,
                "signature": B64.encode(signature),
            }),
        )?;
        let mut st = self.lock();
        st.events_signed = st.events_signed.max(snap.events);
        Ok(())
    }

    /// Sign and append a checkpoint now if any event is unsigned; returns
    /// whether one was written. Blocks for one SLH-DSA signature, so async
    /// code uses [`AuditLog::spawn_checkpointer`] instead.
    // The binary only uses the background checkpointer; tests and library
    // users call this.
    #[allow(dead_code)]
    pub fn checkpoint_now(&self) -> Result<bool> {
        let Some(snap) = self.snapshot() else {
            return Ok(false);
        };
        let signer = self.signer.as_ref().expect("a snapshot implies a signer");
        let msg = checkpoint_message(&snap.log_id, snap.through_seq, &snap.head);
        let sig = signer.sign_hash_based(&msg)?;
        self.write_checkpoint(&snap, &sig)?;
        Ok(true)
    }

    /// Write checkpoints in the background: every `every`, or as soon as
    /// `checkpoint_every` events are unsigned. Signing runs on the blocking
    /// pool, never under the log's lock. `None` for an unsigned log.
    pub fn spawn_checkpointer(
        self: &Arc<Self>,
        every: Duration,
    ) -> Option<tokio::task::JoinHandle<()>> {
        let signer = self.signer.clone()?;
        let log = Arc::clone(self);
        Some(tokio::spawn(async move {
            let mut tick = tokio::time::interval(every);
            tick.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
            loop {
                tokio::select! {
                    _ = tick.tick() => {}
                    _ = log.wake.notified() => {}
                }
                let Some(snap) = log.snapshot() else {
                    continue;
                };
                let msg = checkpoint_message(&snap.log_id, snap.through_seq, &snap.head);
                let signer = Arc::clone(&signer);
                match tokio::task::spawn_blocking(move || signer.sign_hash_based(&msg)).await {
                    Ok(Ok(sig)) => {
                        if let Err(e) = log.write_checkpoint(&snap, &sig) {
                            eprintln!("Failed to write audit checkpoint: {e}");
                        }
                    }
                    Ok(Err(e)) => eprintln!("Failed to sign audit checkpoint: {e}"),
                    Err(e) => eprintln!("Audit checkpoint signing task failed: {e}"),
                }
            }
        }))
    }
}

/// The last line of `file` (without its newline), or `None` if it is empty.
/// A file that does not end with a newline (a write cut short) gets one, so
/// the next line starts cleanly; the partial line counts as the last line.
fn last_line(file: &mut File) -> Result<Option<Vec<u8>>> {
    const CHUNK: u64 = 64 * 1024;
    let len = file.seek(SeekFrom::End(0))?;
    if len == 0 {
        return Ok(None);
    }
    let mut last = [0u8; 1];
    file.seek(SeekFrom::Start(len - 1))?;
    file.read_exact(&mut last)?;
    let ends_with_newline = last[0] == b'\n';
    let end = if ends_with_newline { len - 1 } else { len };

    // Checkpoint lines run to ~23 KB, so search backwards in chunks rather
    // than reading the whole file.
    let mut start = 0;
    let mut cursor = end;
    while cursor > 0 {
        let n = CHUNK.min(cursor);
        cursor -= n;
        let mut chunk = vec![0u8; n as usize];
        file.seek(SeekFrom::Start(cursor))?;
        file.read_exact(&mut chunk)?;
        if let Some(i) = chunk.iter().rposition(|&b| b == b'\n') {
            start = cursor + i as u64 + 1;
            break;
        }
    }
    let mut line = vec![0u8; (end - start) as usize];
    file.seek(SeekFrom::Start(start))?;
    file.read_exact(&mut line)?;
    if !ends_with_newline {
        file.write_all(b"\n")?;
    }
    Ok(Some(line))
}

/// Start the audit log at `path`, hash-chained but unsigned.
// Kept for library users; the binary calls `init_signed`.
#[allow(dead_code)]
pub fn init(path: &str) -> Result<()> {
    init_signed(path, None, 1).map(|_| ())
}

/// Start the audit log at `path`. With `signer`, call
/// [`AuditLog::spawn_checkpointer`] on the result to have checkpoints written.
pub fn init_signed(
    path: &str,
    signer: Option<Arc<PqKeyExchange>>,
    checkpoint_every: u64,
) -> Result<Arc<AuditLog>> {
    let log = AuditLog::open(Path::new(path), signer, checkpoint_every)?;
    AUDIT_LOG
        .set(Arc::clone(&log))
        .map_err(|_| anyhow!("the audit log is already initialised"))?;
    Ok(log)
}

pub fn log_startup(config: &crate::config::Config) {
    write_entry(
        "startup",
        serde_json::json!({
            "version": env!("CARGO_PKG_VERSION"),
            "listen_address": config.proxy.listen.to_string(),
            "pq_algorithm": &config.security.pq_algorithm,
            "sig_algorithm": &config.security.sig_algorithm,
        }),
    );
}

pub fn log_connection(peer: &SocketAddr) {
    write_entry(
        "connection",
        serde_json::json!({
            "peer_address": peer.to_string(),
        }),
    );
}

pub fn log_key_request(peer: &SocketAddr, key_id: &str, size: usize) {
    write_entry(
        "key_request",
        serde_json::json!({
            "peer_address": peer.to_string(),
            "key_id": key_id,
            "size": size,
        }),
    );
}

pub fn log_qkd_key_used(peer: &SocketAddr, key_id: &str) {
    write_entry(
        "qkd_key_used",
        serde_json::json!({
            "peer_address": peer.to_string(),
            "qkd_key_id": key_id,
        }),
    );
}

pub fn log_auth_failure(peer: &SocketAddr, reason: &str) {
    write_entry(
        "auth_failure",
        serde_json::json!({
            "peer_address": peer.to_string(),
            "reason": reason,
        }),
    );
}

/// Audit-log helper for unexpected internal errors. Currently called only
/// from rare paths; `#[allow(dead_code)]` because the bin's hot path goes
/// through `tracing::error!` instead.
#[allow(dead_code)]
pub fn log_error(context: &str, error: &str) {
    write_entry(
        "error",
        serde_json::json!({
            "context": context,
            "error": error,
        }),
    );
}

fn write_entry(event_type: &str, details: Value) {
    if let Some(log) = AUDIT_LOG.get() {
        if let Err(e) = log.record(event_type, details) {
            eprintln!("Failed to write audit log: {e}");
        }
    }
}

/// Result of [`verify_log`].
#[derive(Debug, Default)]
pub struct VerifyReport {
    /// Lines before the first segment written in the older, unchained
    /// format: there is nothing to verify.
    pub legacy_lines: u64,
    /// Lines with a `seq` but no `segment_start` before them: the start of
    /// their run is missing (a copy made by `copytruncate`, or a cut file),
    /// so they cannot be verified.
    pub unanchored_lines: u64,
    pub segments: Vec<SegmentReport>,
    /// Every check that failed. Empty means no check failed, which is not the
    /// same as verified: see [`VerifyReport::verdict`].
    pub problems: Vec<String>,
}

/// The bottom line of a [`VerifyReport`].
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    /// No check failed and every segment has a verified checkpoint.
    Verified,
    /// No check failed, but part of the log could not be verified:
    /// [`VerifyReport::unverified`] says which.
    NotVerified,
    /// A check failed: [`VerifyReport::problems`].
    Failed,
}

impl VerifyReport {
    pub fn verdict(&self) -> Verdict {
        if !self.problems.is_empty() {
            Verdict::Failed
        } else if !self.unverified().is_empty() {
            Verdict::NotVerified
        } else {
            Verdict::Verified
        }
    }

    /// The parts of the log nothing verifies. A chain without a signature
    /// proves nothing: anyone who can write the file can rebuild it.
    pub fn unverified(&self) -> Vec<String> {
        let mut out = Vec::new();
        if self.segments.is_empty() {
            out.push("the log has no segment in the signed format".to_string());
        }
        if self.unanchored_lines > 0 {
            out.push(format!(
                "{} line(s) at the start belong to a run whose first line is missing \
                 (copied with copytruncate, or cut)",
                self.unanchored_lines
            ));
        }
        for (i, seg) in self.segments.iter().enumerate() {
            if !seg.signed {
                out.push(format!(
                    "segment {} (line {}) was written without a persisted identity: \
                     chained, not signed",
                    i + 1,
                    seg.first_line
                ));
            } else if seg.checkpoints == 0 {
                out.push(format!(
                    "segment {} (line {}) has no verified checkpoint",
                    i + 1,
                    seg.first_line
                ));
            }
        }
        out
    }
}

#[derive(Debug)]
pub struct SegmentReport {
    /// 1-based line number of the segment's `segment_start`.
    pub first_line: u64,
    pub log_id: String,
    /// Whether the gateway had a signing key for this segment.
    pub signed: bool,
    /// Lines in the segment, checkpoints included.
    pub lines: u64,
    /// Checkpoints whose signature verified.
    pub checkpoints: u64,
    /// Highest seq covered by a verified checkpoint.
    pub signed_through: Option<u64>,
    /// Events (not checkpoints) after `signed_through`: nothing signs them yet.
    pub unsigned_events: u64,
    /// Line at which the chain stopped matching; nothing after it is checked.
    pub broken_at: Option<u64>,
}

struct Segment {
    report: SegmentReport,
    log_id: [u8; 32],
    head: [u8; 32],
    heads: Vec<[u8; 32]>,
    is_checkpoint: Vec<bool>,
    key_matches: bool,
}

impl Segment {
    fn finish(mut self) -> SegmentReport {
        let from = self.report.signed_through.map_or(0, |s| s + 1) as usize;
        self.report.unsigned_events = self
            .is_checkpoint
            .iter()
            .skip(from)
            .filter(|c| !**c)
            .count() as u64;
        self.report
    }
}

/// Check an audit log against the gateway's SLH-DSA-Shake128f verification
/// key (the last 32 bytes of `proxy.pub`). `Err` only for read errors; every
/// failed check goes into [`VerifyReport::problems`], and
/// [`VerifyReport::verdict`] gives the bottom line.
pub fn verify_log<R: BufRead>(reader: R, slh_dsa_vk: &[u8]) -> Result<VerifyReport> {
    let mut report = VerifyReport::default();
    let mut current: Option<Segment> = None;
    let mut prev_line: Option<Vec<u8>> = None;
    let vk_hex = hex(slh_dsa_vk);

    for (index, line) in reader.split(b'\n').enumerate() {
        let line = line?;
        let n = index as u64 + 1;
        let value: Option<Value> = serde_json::from_slice(&line).ok();
        let event = value
            .as_ref()
            .and_then(|v| v.get("event_type"))
            .and_then(Value::as_str);
        let details = value.as_ref().and_then(|v| v.get("details"));

        let starts_segment = event == Some(SEGMENT_START)
            && details
                .and_then(|d| d.get("format"))
                .and_then(Value::as_str)
                == Some(FORMAT);
        if starts_segment {
            if let Some(done) = current.take() {
                report.segments.push(done.finish());
            }
            let d = details.expect("checked above");
            let expected_tail = prev_line.as_deref().map(|l| hex(&tail_hash(l)));
            let recorded_tail = d
                .get("prev_tail")
                .and_then(Value::as_str)
                .map(str::to_owned);
            if recorded_tail != expected_tail {
                report.problems.push(format!(
                    "line {n}: the segment does not match the line before it: \
                     lines before line {n} were changed or removed"
                ));
            }
            let signed = d.get("signed").and_then(Value::as_bool).unwrap_or(false);
            let key_matches = d.get("slh_dsa_vk").and_then(Value::as_str) == Some(vk_hex.as_str());
            if signed && !key_matches {
                report.problems.push(format!(
                    "line {n}: the segment was signed by a different key than the one given"
                ));
            }
            match d.get("log_id").and_then(Value::as_str).and_then(unhex32) {
                Some(log_id) => {
                    current = Some(Segment {
                        report: SegmentReport {
                            first_line: n,
                            log_id: hex(&log_id),
                            signed,
                            lines: 0,
                            checkpoints: 0,
                            signed_through: None,
                            unsigned_events: 0,
                            broken_at: None,
                        },
                        log_id,
                        head: chain_genesis(&log_id),
                        heads: Vec::new(),
                        is_checkpoint: Vec::new(),
                        key_matches,
                    });
                }
                None => report
                    .problems
                    .push(format!("line {n}: segment_start has no valid log_id")),
            }
        }

        let Some(seg) = current.as_mut() else {
            if !starts_segment {
                if value.as_ref().and_then(|v| v.get("seq")).is_some() {
                    report.unanchored_lines += 1;
                } else {
                    report.legacy_lines += 1;
                }
            }
            prev_line = Some(line);
            continue;
        };
        seg.report.lines += 1;
        if seg.report.broken_at.is_none() {
            check_line(
                seg,
                n,
                &line,
                value.as_ref(),
                event,
                slh_dsa_vk,
                &mut report.problems,
            );
        }
        prev_line = Some(line);
    }
    if let Some(done) = current.take() {
        report.segments.push(done.finish());
    }
    Ok(report)
}

fn check_line(
    seg: &mut Segment,
    n: u64,
    line: &[u8],
    value: Option<&Value>,
    event: Option<&str>,
    slh_dsa_vk: &[u8],
    problems: &mut Vec<String>,
) {
    let expected_seq = seg.heads.len() as u64;
    let seq = value.and_then(|v| v.get("seq")).and_then(Value::as_u64);
    if seq != Some(expected_seq) {
        problems.push(format!(
            "line {n}: expected seq {expected_seq} in segment {}, found {}: \
             a line was removed, inserted, moved or damaged",
            short(&seg.report.log_id),
            seq.map_or("none".to_string(), |s| s.to_string()),
        ));
        seg.report.broken_at = Some(n);
        return;
    }
    seg.head = chain_entry(&seg.head, line);
    seg.heads.push(seg.head);
    let is_checkpoint = event == Some(CHECKPOINT);
    seg.is_checkpoint.push(is_checkpoint);
    if !is_checkpoint {
        return;
    }

    let d = value.and_then(|v| v.get("details"));
    let through = d.and_then(|d| d.get("through_seq")).and_then(Value::as_u64);
    let head = d
        .and_then(|d| d.get("chain_head"))
        .and_then(Value::as_str)
        .and_then(unhex32);
    let sig = d
        .and_then(|d| d.get("signature"))
        .and_then(Value::as_str)
        .and_then(|s| B64.decode(s).ok());
    let (Some(through), Some(head), Some(sig)) = (through, head, sig) else {
        problems.push(format!("line {n}: malformed checkpoint"));
        return;
    };
    if !seg.report.signed {
        problems.push(format!("line {n}: checkpoint in a segment marked unsigned"));
        return;
    }
    if through >= expected_seq || seg.heads[through as usize] != head {
        problems.push(format!(
            "line {n}: checkpoint does not match the log: a line at or before seq {through} \
             of segment {} was changed",
            short(&seg.report.log_id),
        ));
        seg.report.broken_at = Some(n);
        return;
    }
    let msg = checkpoint_message(&seg.log_id, through, &head);
    let valid =
        seg.key_matches && PqKeyExchange::verify_slh_dsa(&msg, &sig, slh_dsa_vk).unwrap_or(false);
    if !valid {
        problems.push(format!(
            "line {n}: checkpoint signature does not verify with the key given"
        ));
        return;
    }
    seg.report.checkpoints += 1;
    seg.report.signed_through = Some(
        seg.report
            .signed_through
            .map_or(through, |s| s.max(through)),
    );
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 || !s.is_ascii() {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(out)
}

fn short(log_id_hex: &str) -> &str {
    &log_id_hex[..log_id_hex.len().min(12)]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;
    use std::path::PathBuf;

    fn temp_log() -> PathBuf {
        std::env::temp_dir().join(format!("pqtg-audit-{}.log", uuid::Uuid::new_v4()))
    }

    fn verify(path: &Path, key: &PqKeyExchange) -> VerifyReport {
        let file = File::open(path).unwrap();
        verify_log(BufReader::new(file), key.slh_dsa_pk_bytes()).unwrap()
    }

    fn lines(path: &Path) -> Vec<String> {
        std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .map(str::to_owned)
            .collect()
    }

    fn write_lines(path: &Path, lines: &[String]) {
        let mut s = lines.join("\n");
        s.push('\n');
        std::fs::write(path, s).unwrap();
    }

    fn event(log: &AuditLog, i: u64) {
        log.record(
            "connection",
            json!({ "peer_address": format!("10.0.0.{i}:4000") }),
        )
        .unwrap();
    }

    /// A signed log: segment_start, three events, a checkpoint, two more events.
    fn signed_log() -> (PathBuf, Arc<PqKeyExchange>) {
        let path = temp_log();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
        for i in 0..3 {
            event(&log, i);
        }
        assert!(log.checkpoint_now().unwrap());
        event(&log, 3);
        event(&log, 4);
        (path, key)
    }

    fn checkpoint_line(seq: u64, through: u64, head: &[u8; 32], sig: &[u8]) -> String {
        serde_json::to_string(&json!({
            "seq": seq,
            "timestamp": "2026-10-29T12:00:00Z",
            "event_type": "checkpoint",
            "details": {
                "through_seq": through,
                "chain_head": hex(head),
                "alg": SIGNATURE_ALG,
                "signature": B64.encode(sig),
            },
        }))
        .unwrap()
    }

    #[test]
    fn signed_log_verifies_and_reports_the_unsigned_tail() {
        let (path, key) = signed_log();
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.verdict(), Verdict::Verified);
        assert_eq!(r.legacy_lines, 0);
        assert_eq!(r.segments.len(), 1);
        let s = &r.segments[0];
        assert!(s.signed);
        assert_eq!(s.lines, 7);
        assert_eq!(s.checkpoints, 1);
        assert_eq!(s.signed_through, Some(3));
        assert_eq!(s.unsigned_events, 2, "the two events after the checkpoint");
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn idle_log_writes_no_second_checkpoint() {
        let path = temp_log();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        let log = AuditLog::open(&path, Some(key), 1000).unwrap();
        event(&log, 1);
        assert!(log.checkpoint_now().unwrap());
        assert!(
            !log.checkpoint_now().unwrap(),
            "no new event, no checkpoint"
        );
        assert!(!log.checkpoint_now().unwrap());
        assert_eq!(checkpoint_count(&path), 1);
        std::fs::remove_file(path).ok();
    }

    fn checkpoint_count(path: &Path) -> usize {
        lines(path)
            .iter()
            .filter(|l| l.contains("\"checkpoint\""))
            .count()
    }

    /// Signing is slow in unoptimised test builds, so wait for the result
    /// instead of assuming a duration.
    async fn wait_for_checkpoints(path: &Path, n: usize) {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(60);
        while checkpoint_count(path) < n {
            assert!(
                tokio::time::Instant::now() < deadline,
                "no checkpoint {n} within 60 s"
            );
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    #[tokio::test]
    async fn background_checkpointer_signs_once_then_stays_idle() {
        let path = temp_log();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
        event(&log, 1);
        let task = log.spawn_checkpointer(Duration::from_millis(20)).unwrap();
        wait_for_checkpoints(&path, 1).await;
        // Fifteen more ticks with nothing new to sign.
        tokio::time::sleep(Duration::from_millis(300)).await;
        task.abort();
        assert_eq!(
            checkpoint_count(&path),
            1,
            "one checkpoint, then nothing while idle"
        );
        assert!(verify(&path, &key).problems.is_empty());
        std::fs::remove_file(path).ok();
    }

    #[tokio::test]
    async fn reaching_the_event_count_wakes_the_checkpointer() {
        let path = temp_log();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        let log = AuditLog::open(&path, Some(Arc::clone(&key)), 3).unwrap();
        // An hour-long interval: its first tick fires at once and covers
        // segment_start; only the event count can cause the second checkpoint.
        let task = log.spawn_checkpointer(Duration::from_secs(3600)).unwrap();
        wait_for_checkpoints(&path, 1).await;
        for i in 0..3 {
            event(&log, i);
        }
        wait_for_checkpoints(&path, 2).await;
        task.abort();
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.segments[0].checkpoints, 2);
        assert_eq!(r.segments[0].unsigned_events, 0);
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn edited_line_is_detected() {
        let (path, key) = signed_log();
        let mut l = lines(&path);
        l[2] = l[2].replace("10.0.0.1", "10.0.0.9");
        write_lines(&path, &l);
        let r = verify(&path, &key);
        assert!(
            r.problems
                .iter()
                .any(|p| p.contains("checkpoint does not match")),
            "{:?}",
            r.problems
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn removed_line_is_detected() {
        let (path, key) = signed_log();
        let mut l = lines(&path);
        l.remove(2);
        write_lines(&path, &l);
        let r = verify(&path, &key);
        assert!(
            r.problems.iter().any(|p| p.contains("expected seq")),
            "{:?}",
            r.problems
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn reordered_lines_are_detected() {
        let (path, key) = signed_log();
        let mut l = lines(&path);
        l.swap(1, 2);
        write_lines(&path, &l);
        assert!(!verify(&path, &key).problems.is_empty());
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn inserted_line_is_detected() {
        let (path, key) = signed_log();
        let mut l = lines(&path);
        let forged = l[2].replace("10.0.0.1", "10.0.0.66");
        l.insert(2, forged);
        write_lines(&path, &l);
        assert!(!verify(&path, &key).problems.is_empty());
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn wrong_key_is_detected() {
        let (path, _) = signed_log();
        let other = PqKeyExchange::new().unwrap();
        let r = verify(&path, &other);
        assert!(
            r.problems.iter().any(|p| p.contains("different key")),
            "{:?}",
            r.problems
        );
        assert_eq!(r.segments[0].checkpoints, 0);
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn forged_signature_is_detected() {
        let (path, key) = signed_log();
        let mut l = lines(&path);
        let mut v: Value = serde_json::from_str(&l[4]).unwrap();
        let mut sig = B64
            .decode(v["details"]["signature"].as_str().unwrap())
            .unwrap();
        sig[100] ^= 1;
        v["details"]["signature"] = json!(B64.encode(sig));
        l[4] = serde_json::to_string(&v).unwrap();
        write_lines(&path, &l);
        let r = verify(&path, &key);
        assert!(
            r.problems
                .iter()
                .any(|p| p.contains("signature does not verify")),
            "{:?}",
            r.problems
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn checkpoint_signed_for_another_log_is_detected() {
        // A genuine signature by the right key, over the right seq and chain
        // head, but for a different log_id: the signed message binds log_id.
        let (path, key) = signed_log();
        let l = lines(&path);
        let log_id = unhex32(
            serde_json::from_str::<Value>(&l[0]).unwrap()["details"]["log_id"]
                .as_str()
                .unwrap(),
        )
        .unwrap();
        let mut head = chain_genesis(&log_id);
        for line in &l {
            head = chain_entry(&head, line.as_bytes());
        }
        let through = l.len() as u64 - 1;
        let other_id = [7u8; 32];
        let sig = key
            .sign_hash_based(&checkpoint_message(&other_id, through, &head))
            .unwrap();
        let mut forged = l.clone();
        forged.push(checkpoint_line(l.len() as u64, through, &head, &sig));
        write_lines(&path, &forged);
        let r = verify(&path, &key);
        assert!(
            r.problems
                .iter()
                .any(|p| p.contains("signature does not verify")),
            "{:?}",
            r.problems
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn legacy_prefix_is_counted_and_linked() {
        let path = temp_log();
        std::fs::write(
            &path,
            "{\"timestamp\":\"2026-01-01T00:00:00Z\",\"event_type\":\"startup\",\"details\":{}}\n\
             {\"timestamp\":\"2026-01-01T00:00:01Z\",\"event_type\":\"connection\",\"details\":{}}\n",
        )
        .unwrap();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
        event(&log, 1);
        log.checkpoint_now().unwrap();
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.legacy_lines, 2);
        assert_eq!(r.segments.len(), 1);

        // Changing the old line right before the segment breaks the link.
        let mut l = lines(&path);
        l[1] = l[1].replace("00:00:01", "00:00:02");
        write_lines(&path, &l);
        let r = verify(&path, &key);
        assert!(
            r.problems
                .iter()
                .any(|p| p.contains("does not match the line before")),
            "{:?}",
            r.problems
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn second_run_links_to_the_first() {
        let path = temp_log();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        {
            let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
            event(&log, 1);
            log.checkpoint_now().unwrap();
            event(&log, 2);
        }
        {
            let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
            event(&log, 3);
            log.checkpoint_now().unwrap();
        }
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.segments.len(), 2);
        assert_eq!(
            r.segments[0].unsigned_events, 1,
            "event 2 was never checkpointed"
        );

        // Dropping the first run's unsigned last event is caught by the link.
        let mut l = lines(&path);
        let i = l.iter().position(|x| x.contains("10.0.0.2")).unwrap();
        l.remove(i);
        write_lines(&path, &l);
        let r = verify(&path, &key);
        assert!(
            r.problems
                .iter()
                .any(|p| p.contains("does not match the line before")),
            "{:?}",
            r.problems
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn unsigned_log_is_chained_but_not_verified() {
        let path = temp_log();
        let log = AuditLog::open(&path, None, 1000).unwrap();
        event(&log, 1);
        assert!(!log.checkpoint_now().unwrap());
        assert!(log.spawn_checkpointer(Duration::from_secs(1)).is_none());
        let key = PqKeyExchange::new().unwrap();
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert!(!r.segments[0].signed);
        assert_eq!(r.segments[0].checkpoints, 0);
        assert_eq!(
            r.verdict(),
            Verdict::NotVerified,
            "a chain alone proves nothing"
        );
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn cut_short_last_line_gets_a_newline() {
        let path = temp_log();
        std::fs::write(&path, "{\"event_type\":\"startup\"").unwrap();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
        event(&log, 1);
        log.checkpoint_now().unwrap();
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.legacy_lines, 1);
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn stripped_checkpoints_are_not_verified() {
        // Without the key nobody can forge a checkpoint, but anyone can drop
        // the checkpoints, renumber and rewrite the rest: the chain is not
        // keyed. That must not read as verified.
        let (path, key) = signed_log();
        let rewritten: Vec<String> = lines(&path)
            .iter()
            .map(|l| serde_json::from_str::<Value>(l).unwrap())
            .filter(|v| v["event_type"] != "checkpoint")
            .enumerate()
            .map(|(i, mut v)| {
                v["seq"] = json!(i);
                serde_json::to_string(&v)
                    .unwrap()
                    .replace("10.0.0.1", "10.0.0.9")
            })
            .collect();
        write_lines(&path, &rewritten);
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.verdict(), Verdict::NotVerified);
        assert!(r.unverified()[0].contains("no verified checkpoint"));
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn unsigned_last_run_is_not_verified() {
        let path = temp_log();
        let key = Arc::new(PqKeyExchange::new().unwrap());
        {
            let log = AuditLog::open(&path, Some(Arc::clone(&key)), 1000).unwrap();
            event(&log, 1);
            log.checkpoint_now().unwrap();
        }
        {
            let log = AuditLog::open(&path, None, 1000).unwrap();
            event(&log, 2);
        }
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.verdict(), Verdict::NotVerified);
        assert!(r.unverified()[0].contains("segment 2"));
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn file_starting_mid_run_is_not_verified() {
        // What copytruncate leaves in the rotated-away copy's successor.
        let (path, key) = signed_log();
        let l = lines(&path);
        write_lines(&path, &l[2..]);
        let r = verify(&path, &key);
        assert!(r.problems.is_empty(), "{:?}", r.problems);
        assert_eq!(r.unanchored_lines, 5);
        assert_eq!(r.legacy_lines, 0);
        assert!(r.segments.is_empty());
        assert_eq!(r.verdict(), Verdict::NotVerified);
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn reserved_event_types_are_refused() {
        let path = temp_log();
        let log = AuditLog::open(&path, None, 1000).unwrap();
        assert!(log.record("checkpoint", json!({})).is_err());
        assert!(log.record("segment_start", json!({})).is_err());
        std::fs::remove_file(path).ok();
    }
}
