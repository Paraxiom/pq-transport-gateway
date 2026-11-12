//! Per-client rate limits for the gateway.
//!
//! Two things an authorized client can make the gateway do without bound,
//! each of which costs something that is not the client's alone:
//!
//! - a handshake: one signature by the gateway's long-term Falcon key, one
//!   ML-KEM encapsulation, and for a hybrid hello one QKD key from the key
//!   manager;
//! - a key request inside a session: one QKD key from the key manager, drawn
//!   from the gateway's default SAE, which every client shares, and one more
//!   signature by the long-term key.
//!
//! A limit on each, per client key, bounds how many signatures any one client
//! can obtain from that key and how fast it can draw down the key manager.
//! On wire 2.1, where a signed request can be replayed by someone else
//! (`docs/THREAT-MODEL.md`, L6), it also bounds what the replay yields.
//!
//! The rule is exact and has no burst allowance on top: a client is allowed
//! an event if fewer than `limit` of its events were allowed during the
//! `window` that ends now. So no window of that length, wherever it starts,
//! holds more than `limit` allowed events of one client. Refused events are
//! not counted: a client that keeps asking while over its limit is not
//! pushed further back.
//!
//! State is one queue of at most `limit` instants per client. Callers pass
//! the id of an authorized key, so the number of queues is bounded by the
//! size of `authorized_keys`.

use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

/// The window of every limit the gateway configures: limits are stated per
/// minute.
pub const ONE_MINUTE: Duration = Duration::from_secs(60);

/// At most `limit` events per client in any `window`.
pub struct ClientLimiter {
    limit: usize,
    window: Duration,
    /// Per client, the instants of its allowed events that are younger than
    /// `window`, oldest first.
    allowed: HashMap<String, VecDeque<Instant>>,
}

impl ClientLimiter {
    /// A limiter that allows each client `per_minute` events in any minute.
    pub fn per_minute(per_minute: u32) -> Self {
        Self::new(per_minute as usize, ONE_MINUTE)
    }

    /// A limiter that allows each client `limit` events in any `window`.
    pub fn new(limit: usize, window: Duration) -> Self {
        Self {
            limit,
            window,
            allowed: HashMap::new(),
        }
    }

    /// The number of events a client is allowed per window.
    pub fn limit(&self) -> usize {
        self.limit
    }

    /// One event for `client` at `now`. `true`, and the event is counted,
    /// when the client is within its limit; `false`, and nothing is counted,
    /// when it is not. `now` must not go back between calls: take it from a
    /// monotonic clock while holding the lock that guards this limiter.
    pub fn allow(&mut self, client: &str, now: Instant) -> bool {
        let events = self.allowed.entry(client.to_string()).or_default();
        // An event leaves the window once it is `window` old: the window
        // that ends at `now` is half-open, `(now - window, now]`.
        while let Some(oldest) = events.front() {
            if now.saturating_duration_since(*oldest) < self.window {
                break;
            }
            events.pop_front();
        }
        if events.len() >= self.limit {
            return false;
        }
        events.push_back(now);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn at(start: Instant, millis: u64) -> Instant {
        start + Duration::from_millis(millis)
    }

    #[test]
    fn a_client_is_allowed_its_limit_and_then_refused() {
        let start = Instant::now();
        let mut limiter = ClientLimiter::per_minute(3);
        assert_eq!(limiter.limit(), 3);
        for i in 0..3 {
            assert!(limiter.allow("a", at(start, i)), "event {i}");
        }
        for i in 3..10 {
            assert!(!limiter.allow("a", at(start, i)), "event {i}");
        }
    }

    /// An allowed event stops counting exactly one window after it happened,
    /// not a millisecond before.
    #[test]
    fn an_event_leaves_the_window_after_one_window_exactly() {
        let start = Instant::now();
        let mut limiter = ClientLimiter::per_minute(2);
        assert!(limiter.allow("a", at(start, 0)));
        assert!(limiter.allow("a", at(start, 10_000)));
        assert!(!limiter.allow("a", at(start, 59_999)));
        // The first event is one minute old: one place is free.
        assert!(limiter.allow("a", at(start, 60_000)));
        assert!(!limiter.allow("a", at(start, 60_001)));
        assert!(!limiter.allow("a", at(start, 69_999)));
        // Then the second.
        assert!(limiter.allow("a", at(start, 70_000)));
        assert!(!limiter.allow("a", at(start, 70_001)));
    }

    /// Asking while over the limit does not push the client further back.
    #[test]
    fn refused_events_are_not_counted() {
        let start = Instant::now();
        let mut limiter = ClientLimiter::per_minute(1);
        assert!(limiter.allow("a", at(start, 0)));
        for i in 1..1_000 {
            assert!(!limiter.allow("a", at(start, i * 50)));
        }
        assert!(limiter.allow("a", at(start, 60_000)));
    }

    #[test]
    fn one_client_does_not_use_up_another_clients_limit() {
        let start = Instant::now();
        let mut limiter = ClientLimiter::per_minute(2);
        assert!(limiter.allow("a", at(start, 0)));
        assert!(limiter.allow("a", at(start, 1)));
        assert!(!limiter.allow("a", at(start, 2)));
        assert!(limiter.allow("b", at(start, 3)));
        assert!(limiter.allow("b", at(start, 4)));
        assert!(!limiter.allow("b", at(start, 5)));
        assert!(!limiter.allow("a", at(start, 6)));
    }

    /// A limit of zero allows nothing. The configuration refuses zero, so
    /// this is what a gateway would do if that check were ever lost: fail
    /// closed.
    #[test]
    fn a_limit_of_zero_allows_nothing() {
        let start = Instant::now();
        let mut limiter = ClientLimiter::per_minute(0);
        assert!(!limiter.allow("a", start));
        assert!(!limiter.allow("a", at(start, 120_000)));
    }

    /// A clock reading that went back is treated as "no time has passed".
    /// It never frees a place early and never panics.
    #[test]
    fn a_clock_reading_that_went_back_frees_nothing() {
        let start = Instant::now();
        let mut limiter = ClientLimiter::per_minute(1);
        assert!(limiter.allow("a", at(start, 30_000)));
        assert!(!limiter.allow("a", at(start, 0)));
        assert!(!limiter.allow("a", at(start, 89_999)));
        assert!(limiter.allow("a", at(start, 90_000)));
    }

    /// The reference: every decision recomputed from the whole history. An
    /// event is allowed exactly when fewer than `limit` earlier allowed
    /// events of the same client are younger than the window.
    fn reference(limit: usize, window_ms: u64, events: &[(u8, u64)]) -> Vec<bool> {
        let mut allowed: Vec<(u8, u64)> = Vec::new();
        let mut verdicts = Vec::with_capacity(events.len());
        for &(client, t) in events {
            let recent = allowed
                .iter()
                .filter(|(c, when)| *c == client && t - *when < window_ms)
                .count();
            let ok = recent < limit;
            if ok {
                allowed.push((client, t));
            }
            verdicts.push(ok);
        }
        verdicts
    }

    /// Events of a few clients at non-decreasing times: gaps from 0 ms (a
    /// burst) to longer than the window.
    fn runs() -> impl Strategy<Value = Vec<(u8, u64)>> {
        prop::collection::vec(
            (0u8..3, prop_oneof![Just(0u64), 0u64..40, 0u64..1_500]),
            0..300,
        )
        .prop_map(|steps| {
            let mut t = 0u64;
            steps
                .into_iter()
                .map(|(client, gap)| {
                    t += gap;
                    (client, t)
                })
                .collect()
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            failure_persistence: None,
            ..ProptestConfig::default()
        })]

        /// The limiter decides every event as the reference does.
        #[test]
        fn the_limiter_matches_the_reference(limit in 0usize..6, events in runs()) {
            const WINDOW_MS: u64 = 1_000;
            let start = Instant::now();
            let mut limiter = ClientLimiter::new(limit, Duration::from_millis(WINDOW_MS));
            let expected = reference(limit, WINDOW_MS, &events);
            for (i, &(client, t)) in events.iter().enumerate() {
                let got = limiter.allow(&client.to_string(), at(start, t));
                prop_assert_eq!(got, expected[i], "event {} of client {} at {} ms", i, client, t);
            }
        }

        /// The property the limit is for, checked on what the limiter itself
        /// allowed: no window of one window's length, wherever it starts,
        /// holds more than `limit` allowed events of one client. And a client
        /// is never refused while it has a free place.
        #[test]
        fn no_window_holds_more_than_the_limit(limit in 1usize..6, events in runs()) {
            const WINDOW_MS: u64 = 1_000;
            let start = Instant::now();
            let mut limiter = ClientLimiter::new(limit, Duration::from_millis(WINDOW_MS));
            let mut allowed: Vec<(u8, u64)> = Vec::new();
            for &(client, t) in &events {
                let in_window = allowed
                    .iter()
                    .filter(|(c, when)| *c == client && t - *when < WINDOW_MS)
                    .count();
                if limiter.allow(&client.to_string(), at(start, t)) {
                    allowed.push((client, t));
                } else {
                    prop_assert_eq!(in_window, limit, "refused with a free place at {} ms", t);
                }
            }
            // Every window that starts at an allowed event: [t, t + window).
            for &(client, t) in &allowed {
                let count = allowed
                    .iter()
                    .filter(|(c, when)| *c == client && *when >= t && *when - t < WINDOW_MS)
                    .count();
                prop_assert!(count <= limit, "{} events of client {} from {} ms", count, client, t);
            }
        }
    }
}
