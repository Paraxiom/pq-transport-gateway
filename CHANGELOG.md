# Changelog

## Unreleased

### Wire 2.1 is off by default (2026-11-12)

- **Breaking for wire 2.1 clients.** A gateway accepts the wire versions
  listed in `proxy.versions`, `["3.2"]` by default. A 2.1 hello is refused at
  its version field unless the operator lists `"2.1"`. A client that still
  speaks 2.1 also needs `wire=2.1` on its `authorized_keys` line.
  **Before upgrading a gateway that serves a 2.1 client**, add
  `versions = ["3.2", "2.1"]` under `[proxy]` and `wire=2.1` to that client's
  line. Without both the client is refused, and the gateway log says which
  of the two is missing. A gateway whose clients all speak 3.2 needs no
  change.
- **One wire version per key.** A key without the option speaks 3.2 only. A
  key with `wire=2.1` speaks 2.1 only and is refused on 3.2. When a client
  moves to 3.2 the operator removes the option.
- **Why.** The 2.1 hello is not signed. Anyone who knows a client's two
  public keys can open a 2.1 session in its name, and a key request that
  client signed once is accepted again in that session, since the signature
  covers the request bytes only (`docs/THREAT-MODEL.md`, L6). Until now this
  was a reading of the code. It is now a test:
  `on_wire_2_1_a_signed_request_is_served_again_to_someone_else` serves a
  key, twice, to the holder of one signed request and of the public keys.
  Until now every gateway accepted 2.1, and one `authorized_keys` line
  admitted a client on both versions, so a request signed in a 3.2 session
  could be replayed in a 2.1 session too.
- **What stays open.** A key marked `wire=2.1` on a gateway that lists
  `"2.1"`. Requests from such keys are not rate limited yet.
- `authorized_keys`: the options `perm=` and `wire=` may come in either
  order, each once. A line with a repeated option or a `wire=` value that
  is not `2.1` or `3.2` is dropped with a warning, so that key is not
  authorized at all. The comment now begins right after the options: its
  first word used to be lost on a line without `perm=`.
- `proxy.versions` is checked at startup: an empty list, a version the
  gateway does not speak, or a version listed twice stops the gateway with
  the reason. At startup the gateway logs the versions it accepts and the
  number of keys for each, and warns when 2.1 is on, when a version is on
  with no key for it, and when keys are registered for a version that is
  off.
- A refusal by the switch is logged and costs the gateway nothing else. A
  listed key presented on the wrong version is refused before any
  encapsulation and recorded in the audit log.
- Tests: `tests/gateway_session.rs` (`wire_2_1_is_refused_by_default`,
  `a_key_marked_for_2_1_needs_the_gateway_switch_too`,
  `where_2_1_is_on_each_key_speaks_one_version`, the two replay tests
  above); `config.rs` (`wire_2_1_is_off_by_default`,
  `wire_2_1_is_on_only_when_listed`,
  `a_bad_version_list_is_refused_at_startup`); `auth.rs` (four tests of the
  `wire=` option); `proxy.rs` (three tests of the two checks). The fuzz
  target `server_hello_path` lists both versions and uses one key per
  version, so both hello paths stay reachable.

### Hello replay guard: the window was one second too short (2026-11-12)

- **The defect.** The gateway admits a v3 hello when its signed timestamp is
  within `hello_max_skew_secs` of the server clock and the replay guard has
  not seen it. The guard remembered a hello for `2 × skew` seconds. The
  timestamp check works in whole seconds, so a timestamp is acceptable
  during `2 × skew + 1` seconds of real time. A hello first seen when it
  was dated exactly `skew` seconds ahead of the server was forgotten during
  the last second in which its timestamp still passed, and a copy presented
  in that second was admitted again. The relay hello had the same window
  (`HELLO_REPLAY_WINDOW`) and the same gap.
- **What it cost.** Gateway: one more QKD key allocation and one more
  encapsulation per replayed hello. Relay: one more handshake served. At
  most once per hello, and only for a hello dated at the far edge of the
  allowed skew. No secret: only the honest client can decapsulate. An
  attacker has to record such a hello and present it again about
  `2 × skew` seconds later, inside a window of at most one second.
- **The fix.** `ReplayGuard::window_for_skew` gives a window of
  `2 × skew + 2` seconds: one second for the whole-second comparison, one
  for the time between reading the clocks and reaching the guard. The
  gateway builds its guard with `ReplayGuard::for_skew`; the relay's
  `HELLO_REPLAY_WINDOW` is `ReplayGuard::window_for_skew(HELLO_MAX_SKEW_SECS)`.
  The arithmetic saturates on an absurd skew instead of wrapping to a short
  window. No configuration change and no wire change.
- Tests: `v3_hello_first_seen_at_the_early_edge_is_still_refused_at_the_late_edge`
  (gateway) and
  `the_replay_window_covers_the_whole_interval_a_hello_is_acceptable`
  (relay); both fail with the old window.
  `a_guard_for_a_skew_remembers_through_the_last_acceptable_second`,
  `the_window_for_a_skew_covers_the_whole_acceptance_interval`.
- Limits that remain: a restart empties the guard, so a hello admitted in
  the last window can be admitted once more after a restart; a server wall
  clock set back during the window makes old timestamps acceptable again.

### Input checks on the key manager side (2026-11-11)

- **SAE IDs are restricted.** An SAE ID becomes a path segment of the key
  manager URL (`/api/v1/keys/{SAE_ID}/...`). It is now limited to ASCII
  letters, digits and `-`, `_`, `.`, `:`, at most 256 bytes, and may not be
  `.` or `..`. It is checked in the configuration, when a v3 hello arrives
  (a malformed one refuses the hello; it no longer falls back to PqcOnly),
  and before each key manager URL is built. A deployment whose SAE IDs use
  other characters must be checked before upgrading: the gateway refuses
  them with a clear error.
- **The "vendor API on localhost" check parses the URL.** The host must be
  `localhost`, an address in 127.0.0.0/8, or `::1`. The earlier check looked
  for the text "localhost" anywhere in the string. A URL with a user name or
  password is refused.
- **paraxiom-pqc 0.2.1** (lock file only), which brings ml-kem 0.3.3.

### Signed audit log (issue #9)

Until now the audit log was written as unsigned JSON lines, and
`docs/THREAT-MODEL.md` listed tampering with it (T9) as not mitigated.

- Each gateway run starts a segment (`segment_start`, with a random
  `log_id`), and its lines form a hash chain over their exact bytes.
- After `audit_checkpoint_events` events (default 1000) or
  `audit_checkpoint_secs` seconds (default 300), the gateway signs the chain
  head with its SLH-DSA-Shake128f identity key in a `checkpoint` line of
  about 23 KB. An idle gateway writes none. Only a persisted identity signs;
  with an ephemeral one the log is chained and marked unsigned.
- A segment records a hash of the line before it, so a change to the end of
  an earlier run is caught too.
- `pq-qkd-proxy --verify-audit-log <log> [proxy.pub]` checks a log. It exits
  0 only when no check failed and every segment has a verified checkpoint, 1
  when a check fails, and 2 when part of the log cannot be verified: a run
  without a persisted identity, a run with no checkpoint, or a file that
  starts mid-run. A chain without a signature proves nothing, since anyone
  who can write the file can rebuild it. Rotate the log by renaming it, not
  with `copytruncate`.
- Every line now carries a `seq` field, and `segment_start` and `checkpoint`
  are new event types. Lines written by earlier versions are reported as
  legacy, not verified.
- New domains `audit/v1/{genesis,entry,checkpoint,tail}`, with vectors in
  `tests/vectors/audit-v1.json` from the independent Python generator.
- Library: `ProxyServer::with_identity`, `ProxyServer::load_identity`,
  `audit::init_signed` and `audit::AuditLog`.

T9 is now "Detected, with limits": the key is a file on the same host, so
whoever controls the host can re-sign a forged log; events after the last
checkpoint are unsigned until the next one; and removing the end of the
file, its last checkpoint included, cannot be detected from the file alone.

### Fixed

- `audit_enabled = false` was ignored: the gateway wrote its audit log
  anyway. It now writes none and warns at startup
  (`tests/audit_enabled.rs`).
- `docs/THREAT-MODEL.md` and `docs/CLIENT-INTEGRATION.md` linked issues
  #1, #2, #3 and #7 of an earlier tracker; on this repository those numbers
  are other pull requests and issues. The links are replaced by what they
  referred to. Per-source DoS limits (S7, T11) are not yet tracked in a
  public issue.

## 3.0.0 (2026-10-15)

3.0.0 because the gateway's wire versions change: a 3.0.0 gateway and a 2.x
gateway or client do not interoperate. Upgrade every gateway and every client
together.

### Security: the gateway session reused AES-GCM nonces

In 2.0.0, and on `main` through e50204d, the gateway session layer
(`PqSession` in `src/crypto.rs`) used one AES-256-GCM key, the handshake's
session key, for both directions, and both ends counted nonces from 0. A
client following `docs/CLIENT-INTEGRATION.md` sealed its first request under
the same key and nonce as the gateway's first response, and so on at every
position. That exposes the XOR of the two plaintexts and lets an observer
recover the GHASH authentication key of the session. The receiver also
accepted any nonce, so frames could be replayed or reordered within a
session. Details and recommended action: `SECURITY.md`, advisory of
2026-10-14.

Fixed (70be762):

- The session key is expanded into one key per direction, under distinct,
  versioned domains (`gateway/v2/key/{c2s,s2c}`, `gateway/v3/key/{c2s,s2c}`).
- Each direction keeps its own counter from 0, which never wraps.
- Each end accepts only the next expected frame, so replayed, reordered and
  reflected frames are refused.
- The handshakes and their key schedules are unchanged. Specified in
  `docs/KEY-SCHEDULE.md` §5, with vectors in
  `tests/vectors/gateway-session.json`.

The relay (`src/relay.rs`, wire `relay-4`) was not affected and is unchanged.

### Breaking: wire versions

- The gateway speaks `2.1` (v2 handshake) and `3.2` (v3 handshake). It
  refuses hellos for `2.0`, `3.0` and `3.1`, and a client following the
  updated `docs/CLIENT-INTEGRATION.md` §2 step 4 refuses a server that answers
  with an older version. A mismatch fails closed; nothing falls back to the
  old session layer.
- Deployments must move together. In particular the gateways at site 101 and
  on the KR260 must be upgraded at the same time as the clients that talk to
  them. A 3.0.0 gateway refuses the hellos of 2.x clients. A 2.x gateway
  accepts any hello whose version starts with `2.`, so it does answer a
  3.0.0 client's `2.1` hello, but with `2.0`; a 3.0.0 client following
  `docs/CLIENT-INTEGRATION.md` refuses that ServerHello, and the two ends'
  frame keys differ (3.0.0 derives one key per direction), so no frame
  would decrypt in any case.
- The identity file format (`proxy.key`) and `authorized_keys` entries are
  unchanged. Checked on this machine with two freshly generated identities:
  one from the published 2.0.0 crate (with `paraxiom-pqc` 0.1.2) and one from
  the pre-release tree at dad0a0a (with 0.1.3). Each loads in 3.0.0, signs and
  verifies; for the dad0a0a one, 3.0.0 also prints the same fingerprint as the
  code that made it. Not checked with the identity files on the deployed
  hosts.
- An identity whose Falcon-512 key does not have the expected length and
  header (secret key 1281 bytes starting `0x59`, public key 897 bytes
  starting `0x09`), or whose verification keys carry another algorithm, is
  now refused when it is loaded. Before, under `paraxiom-pqc` 0.2.0, such a
  file would load and every handshake would then fail when signing. Both
  identities above pass the check. On a deployed host,
  `xxd -s 6 -l 5 proxy.key` prints `0000 0501 59` for a well-formed file.

### Dependencies: paraxiom-pqc 0.2.0

- `paraxiom-pqc` comes from crates.io, version `0.2`, instead of a git
  revision (0.1.3, c0ee1f7). The ML-DSA and SLH-DSA code it vendors arrives as
  `paraxiom-ml-dsa` 0.1.0-rc.7 and `paraxiom-slh-dsa` 0.2.0-rc.4. No crate that
  compiles C was added.
- 0.2.0 clears its secret key types and shared secrets from memory when they
  are dropped. In the gateway this covers the long-term Falcon-512 and
  SLH-DSA signing keys in `PqKeyExchange` and the ML-KEM decapsulation key in
  `EphemeralKemKey`. It does not cover the copies listed under known limits.
- 0.2.0 checks that a Falcon key's header and length match the degree its
  label names. The gateway generates, stores and pins only Falcon-512 keys
  labelled Falcon-512, so its keys pass; two new tests in `src/crypto.rs`
  check the headers of generated keys and that a key of another degree never
  verifies (a Falcon-1024 key passed as Falcon-512 was accepted with 0.1.3).
- 0.2.0 refuses to create Falcon keys or sign with them on targets other
  than x86/x86_64 with SSE2 and AArch64 with NEON. Gateways and clients both
  sign with Falcon. Built and tested on macOS arm64 only; not tested on the
  KR260 (AArch64) or any other target.

### Since 2.0.0, already on `main` before this release

2.0.0 on crates.io was built from 1e109c3, a commit that is not in the
history of this branch; it speaks wire `2.0` only. Compared with it, 3.0.0
also has the following (see the git history of `main` for each):

- Wire protocol v3: the ETSI 014 `key_ID`, key mode, master SAE-ID and key
  length bound under the transcript signature; the client signs its hello;
  freshness and replay guard on v3 hellos (`docs/PROTOCOL-V3-QKD-KEYID.md`).
- Hardened key schedule for v3 and the relay: domain tree and keyed chaining
  KDF (`docs/KEY-SCHEDULE.md`).
- The post-quantum TCP relay (`src/relay.rs`), with server pinning and client
  authentication.
- Single-use ephemeral KEM keys, one-time zeroized QKD keys, and the server
  handshake as a type-state machine.
- Licence: GPL-3.0-only, or a Paraxiom commercial licence (`LICENSE.md`).
  2.0.0 was published as MIT OR Apache-2.0.

### Tests and checks added on this branch

Property tests, key-leak tests, payload tests and fuzz targets for the
session layer, Verifpal models and Kani harnesses. What each one ran and
found is in `formal/GATEWAY-SESSION-RESULTS-2026-10-15.md`; of the seven Kani
harnesses, one reached a verdict. None of this is an external audit or a
proof of the cryptographic code. Those runs used `paraxiom-pqc` 0.1.3 and
were not repeated on 0.2.0.

### Known limits

- **Replay under a one-direction key leak (THREAT-MODEL L6).** The Falcon
  signature inside each gateway frame covers the data only, not the session,
  direction or position. If an attacker learns `k_c2s`, it can re-seal a
  request the client really signed at a later position of the same session,
  or into another session whose `k_c2s` it also holds, and the gateway
  accepts it. It still cannot forge a request the client never signed, and
  the other direction is unaffected. Closing this needs a wire change; not
  done.
- **Memory wiping gaps (THREAT-MODEL T12).** Not wiped, among others: the
  32-byte ML-KEM shared secret copies returned by `encapsulate_to` and
  `EphemeralKemKey::decapsulate` and held through the handshake, the v2
  QKD-mixed secret, the handshake `session_key`, the AES key schedules inside
  `Aes256Gcm` (`aes-gcm` is built without its `zeroize` feature), and the
  buffers that hold an encoded identity while it is saved or loaded. Identity
  keys are stored unencrypted on disk (mode 0o600).
- Not externally audited.

### Other

- Inline format arguments flagged by clippy 1.88; messages unchanged.

## 2.0.0

Wire-incompatible with 1.0.0: real ML-KEM-768 key encapsulation replaces the
signature-only "shared secret" of 1.0.0, which did not produce a shared
secret. 1.0.0 is yanked. 2.0.0 is affected by the nonce reuse fixed in 3.0.0.
