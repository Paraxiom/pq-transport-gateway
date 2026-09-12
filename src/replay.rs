//! Replay guard for the v3 ClientHello (backlog B8).
//!
//! A signed hello proves who sent it and binds its KEM key (B6), but a
//! recorded honest hello verifies just as well the second time: the server
//! contributes nothing before accepting it. Verifpal reports exactly that
//! (`formal/CLIENTAUTH-RESULTS-2026-09-12.md`). No secret is at stake, since
//! only the honest client can decapsulate, but every replay costs the server
//! one QKD key allocation and one encapsulation.
//!
//! Two checks close it without a third message:
//!
//! 1. the hello carries a signed `timestamp`; the server rejects anything
//!    outside `±max_skew` of its own clock, so a recording is worthless once
//!    the skew window has passed;
//! 2. inside the window, this guard remembers every `client_random` it has
//!    admitted and refuses a second sight.
//!
//! Memory is therefore bounded by handshake rate × window, and capped. Only
//! signature-valid, in-window hellos are ever inserted, so an attacker without
//! an authorized client's private key cannot fill the cache; hitting the cap
//! means legitimate load exceeds the sizing, and the guard fails closed rather
//! than quietly reopening the replay window.

use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

/// Outcome of presenting a hello identifier to the guard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Never seen inside the window; now remembered.
    Fresh,
    /// Already admitted inside the window.
    Replay,
    /// Not seen, but the cache is at capacity. Fail closed.
    Full,
}

/// Bounded, time-windowed set of admitted hello identifiers.
pub struct ReplayGuard {
    window: Duration,
    max_entries: usize,
    seen: HashMap<[u8; 32], Instant>,
    /// Insertion order, which is also time order, so expiry sweeps the front.
    order: VecDeque<([u8; 32], Instant)>,
}

impl ReplayGuard {
    /// `window` should be twice the accepted clock skew: a hello stamped `t` is
    /// acceptable while the server clock is within `[t - skew, t + skew]`, so
    /// the guard has to remember it for up to `2 * skew` after first sight.
    pub fn new(window: Duration, max_entries: usize) -> Self {
        Self {
            window,
            max_entries,
            seen: HashMap::new(),
            order: VecDeque::new(),
        }
    }

    /// Present an identifier at time `now`. Expired entries are swept first,
    /// so a full cache made of stale entries does not refuse anyone.
    pub fn check_and_insert(&mut self, id: [u8; 32], now: Instant) -> Verdict {
        self.sweep(now);
        if self.seen.contains_key(&id) {
            return Verdict::Replay;
        }
        if self.seen.len() >= self.max_entries {
            return Verdict::Full;
        }
        self.seen.insert(id, now);
        self.order.push_back((id, now));
        Verdict::Fresh
    }

    fn sweep(&mut self, now: Instant) {
        while let Some((id, seen_at)) = self.order.front() {
            if now.duration_since(*seen_at) < self.window {
                break;
            }
            let id = *id;
            self.order.pop_front();
            self.seen.remove(&id);
        }
    }

    pub fn len(&self) -> usize {
        self.seen.len()
    }

    // Used by tests and by the library API; the binary never asks, hence the
    // bin-side allow (same reason as `EphemeralKemKey` in crypto.rs).
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.seen.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(b: u8) -> [u8; 32] {
        [b; 32]
    }

    #[test]
    fn a_fresh_id_is_admitted_once_and_then_seen_as_a_replay() {
        let mut g = ReplayGuard::new(Duration::from_secs(240), 8);
        let t0 = Instant::now();
        assert_eq!(g.check_and_insert(id(1), t0), Verdict::Fresh);
        assert_eq!(g.check_and_insert(id(1), t0), Verdict::Replay);
        assert_eq!(
            g.check_and_insert(id(1), t0 + Duration::from_secs(239)),
            Verdict::Replay,
            "still remembered just inside the window"
        );
        assert_eq!(g.len(), 1);
    }

    #[test]
    fn an_id_is_forgotten_once_the_window_has_passed() {
        // Forgetting is safe ONLY because the timestamp check makes the same
        // hello unacceptable by then; the guard alone is not the whole story.
        let mut g = ReplayGuard::new(Duration::from_secs(240), 8);
        let t0 = Instant::now();
        assert_eq!(g.check_and_insert(id(1), t0), Verdict::Fresh);
        assert_eq!(
            g.check_and_insert(id(1), t0 + Duration::from_secs(240)),
            Verdict::Fresh
        );
    }

    #[test]
    fn distinct_ids_do_not_interfere() {
        let mut g = ReplayGuard::new(Duration::from_secs(240), 8);
        let t0 = Instant::now();
        assert_eq!(g.check_and_insert(id(1), t0), Verdict::Fresh);
        assert_eq!(g.check_and_insert(id(2), t0), Verdict::Fresh);
        assert_eq!(g.check_and_insert(id(2), t0), Verdict::Replay);
        assert_eq!(g.len(), 2);
    }

    #[test]
    fn the_cap_fails_closed_but_expired_entries_free_their_slots() {
        let mut g = ReplayGuard::new(Duration::from_secs(240), 2);
        let t0 = Instant::now();
        assert_eq!(g.check_and_insert(id(1), t0), Verdict::Fresh);
        assert_eq!(g.check_and_insert(id(2), t0), Verdict::Fresh);
        assert_eq!(
            g.check_and_insert(id(3), t0),
            Verdict::Full,
            "a third distinct id inside the window must be refused, not admitted"
        );
        // A replay is still reported as a replay, never as Full.
        assert_eq!(g.check_and_insert(id(1), t0), Verdict::Replay);
        // Once the first two expire, the slot is free again.
        assert_eq!(
            g.check_and_insert(id(3), t0 + Duration::from_secs(240)),
            Verdict::Fresh
        );
        assert_eq!(g.len(), 1);
    }
}
