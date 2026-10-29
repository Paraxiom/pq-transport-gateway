# PQTG Threat Model

**Version**: aligned with PQTG `0.2.0` and `paraxiom-pqc` `0.1.1`.
**Audience**: ETSI ISG-QKD reviewers, KirQ engineers, security consultants
performing third-party review.

This document states what PQTG protects, what it does not, the threats it
considers, and the mitigation each threat reduces to. It is deliberately
short. Where a property is *proved*, *assumed*, or *argued but not proved*,
that distinction is called out.

---

## 1. System under analysis

PQTG sits on the same host as a QKD vendor's Key Management Entity (KME)
and exposes a quantum-safe API to remote clients. The vendor's TLS-based
ETSI GS QKD 014 endpoint is not exposed beyond `localhost`.

```
┌─────────────────────────────┐         ┌──────────────────┐
│   Host running PQTG + KME   │         │  Remote client   │
│                             │         │   (QSSH, etc.)   │
│  ┌────────┐    ┌──────────┐ │   PQ    │                  │
│  │ vendor │ ←→ │  PQTG    │ │ ←─────→ │ ML-KEM-768       │
│  │  KME   │  loopback     │ │  Falcon │ Falcon-512       │
│  │ (TLS)  │   ETSI 014    │ │  +AEAD  │ SLH-DSA-Shake128f│
│  └────────┘    └──────────┘ │         └──────────────────┘
└─────────────────────────────┘
```

External access flows: client → PQTG (post-quantum handshake + AEAD) →
PQTG → vendor KME (loopback TLS, ETSI 014 v1.1.1).

## 2. Trust assumptions

Listed by what they cost us if violated.

| # | Assumption                                                                          | Cost if violated                                |
|---|-------------------------------------------------------------------------------------|-------------------------------------------------|
| A1| The host OS isolates PQTG from co-resident processes.                               | Local privilege escalation reads keys/secrets.  |
| A2| The loopback link to the vendor KME is not observable by other host processes.      | Localhost adversary reads vendor TLS plaintext. |
| A3| The vendor KME correctly delivers QKD key material per ETSI 014.                    | PQTG ships compromised QKD keys to clients.     |
| A4| Authorized clients' Falcon-512 + SLH-DSA-Shake128f public keys are pre-distributed via a trusted out-of-band channel. | Attacker authorizes itself.        |
| A5| ML-KEM-768 is IND-CCA secure (FIPS 203).                                            | KEM-derived session keys recoverable.           |
| A6| Falcon-512 is EUF-CMA secure (Falcon submission, pending FIPS 206).                 | Forgeable handshake transcript signatures.      |
| A7| SLH-DSA-Shake128f is EUF-CMA secure (FIPS 205).                                     | None today: nothing is signed with SLH-DSA (S4).|
| A8| AES-256-GCM is IND-CCA secure under nonce-respecting use (NIST SP 800-38D).         | Session traffic decryptable / forgeable.        |
| A9| SHA3-256 is collision-resistant and behaves as a random oracle for KDF purposes.    | Transcript collisions / KDF weaknesses.         |
|A10| The `paraxiom-pqc` crate (not externally audited) correctly implements A5–A8.       | All cryptographic guarantees collapse.          |

A1 and A2 together define the **localhost trust boundary**.
A5–A9 are inherited; PQTG does not re-derive them.
A10 is a software-supply-chain assumption. `paraxiom-pqc` has not been
externally audited (`SECURITY.md`). It builds on the RustCrypto `ml-kem`,
`ml-dsa` and `slh-dsa` crates and on `falcon-rs`; the three RustCrypto crates
state in their READMEs that they have never been independently audited.
Since 3.0.0 PQTG takes `paraxiom-pqc` from crates.io as `"0.2"` (0.2.0 in
`Cargo.lock`), with its vendored ML-DSA and SLH-DSA code published as
`paraxiom-ml-dsa` 0.1.0-rc.7 and `paraxiom-slh-dsa` 0.2.0-rc.4 and pinned by
`paraxiom-pqc` with `=` versions. `kani/Cargo.toml` names the same version and
`fuzz/` inherits it through its path dependency on the gateway; `fuzz/` has
its own, uncommitted lock, so check what it resolves before a fuzz run. Before
3.0.0 the dependency was a git revision: unpinned until 2026-10-15, then
pinned to c0ee1f7 (0.1.3). 2.0.0 on crates.io used 0.1.2 from crates.io.
The fuzzing and Kani results in `formal/GATEWAY-SESSION-RESULTS-2026-10-15.md`
were obtained with 0.1.3. A `"0.2"` requirement accepts later 0.2.x releases:
a crate that depends on PQTG, or `cargo install` without `--locked`, may
resolve one; `cargo install --locked` uses the published `Cargo.lock`.

## 3. Scope

### In scope (PQTG defends these)

- **S1** Confidentiality of QKD-delivered key material between vendor KME
  and authorized PQTG clients across the public network.
- **S2** Authentication of clients to PQTG via Falcon-512 + SLH-DSA-Shake128f
  verification keys (`authorized_keys`). Both keys are matched against the
  file; only the Falcon-512 key is ever used to verify a signature (the v3
  hello signature and the per-frame signatures), never the SLH-DSA key.
  *Enforced by the `authorized_keys` check:
  unauthorized peers are rejected before any keypair generation,
  fail-closed on empty file. Covered by `auth::tests` (7 unit tests).*
- **S3** Authentication of PQTG to clients via server-side Falcon-512
  signature over the full handshake transcript.
- **S4** Integrity of the audit log. *Status: detected, with limits (T9).
  Each run's lines form a hash chain, and the gateway signs the chain head
  with its SLH-DSA-Shake128f key in `checkpoint` lines (`src/audit.rs`);
  `--verify-audit-log` checks a log against `proxy.pub`.*
- **S5** Forward secrecy of past sessions if the long-term Falcon signing
  key is compromised at a *future* time (achieved via per-handshake
  ephemeral ML-KEM keypair).
- **S6** Mutual binding of session to fresh randomness from both sides
  (`client_random` and `server_random` in the transcript hash).
- **S7** Resistance to handshake flooding from a bounded set of unauthorized
  sources (per-source rate limit + cookie-PoW pre-handshake).
  *Status: in-scope as of 2026-05-05; mitigations not yet shipped, and not
  yet tracked in a public issue.*

### Out of scope

- **O1** The vendor's QKD physical layer (BB84 fidelity, QBER, side-channels
  on the photonic apparatus). PQTG protects key delivery, not key
  generation.
- **O2** OS-level side channels (Spectre/Meltdown, cache timing, EM, power).
- **O3** Distributed DoS from a large unbounded attacker IP space (botnet-class).
  S7 covers single-source / small-source-set handshake flooding; full
  L7 DDoS resistance requires a fronting load-balancer or CDN tier and
  is the deployer's responsibility.
- **O4** Key escrow / recovery. PQTG does not implement key escrow.
- **O5** Quantum-safe distribution of `authorized_keys`. Assumed
  pre-deployed via a secure out-of-band channel (e.g. signed deployment
  manifest, hardware HSM provisioning).
- **O6** Vendor KME compromise (e.g. forged TLS cert before PQTG). PQTG
  treats the vendor KME as a trust anchor; if the KME itself ships bad
  keys, PQTG cannot detect it.

## 4. Threats and mitigations

| # | Threat                                                                       | Status         | Mitigation                                                                                                                                                                                            |
|---|------------------------------------------------------------------------------|----------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|T1 | **Passive network observer** records ciphertext, attempts later decryption. | Mitigated      | All wire traffic is AES-256-GCM under a session key derived from ML-KEM-768 + transcript hash. A5 + A8 are sufficient.                                                                                |
|T2 | **Active network MITM** forges or alters handshake messages.                 | Mitigated      | Server signs the *full* transcript with Falcon-512 (`crypto.rs::sign_transcript`); client verifies (`crypto.rs::verify_falcon`). Tampering changes the transcript, which the signature won't match.   |
|T3 | **Future Falcon SK compromise** (long-term key leaks years later).           | Mitigated (S5) | Each handshake uses a fresh ephemeral ML-KEM keypair (`crypto.rs::EphemeralKemKey`). Past `kem_ss` cannot be recovered from a future Falcon SK leak. **Argued, not formally proved**.                 |
|T4 | **Current Falcon SK compromise** (long-term key leaks now).                  | Detected       | Future authentication breaks (any new session can be forged), but past sessions remain confidential per T3. Operators must rotate via `--generate-keys` and update `authorized_keys` distribution.    |
|T5 | **Replay** of recorded handshake to either side.                             | Mitigated      | Both `client_random` and `server_random` are 32-byte fresh values bound into the transcript hash (`transcript_hash`). A repeat transcript would require both sides to re-emit the same randoms.       |
|T6 | **Algorithm downgrade** to weaker primitives.                                | Mitigated      | Algorithms are not negotiated. The gateway accepts exactly wire `2.1` and `3.2` (`proxy.rs::handshake_for_version`) and refuses every other version at the hello. ML-KEM-768, Falcon-512, SLH-DSA-Shake128f, AES-256-GCM are compile-time constants in `crypto.rs`. |
|T7 | **Harvest-now-decrypt-later** quantum adversary.                             | Mitigated      | All cryptographic primitives are post-quantum (FIPS 203/204/205). No classical KEX (DH/ECDH) anywhere in the wire path. Loopback TLS to the vendor is *out* of scope per O6.                          |
|T8 | **`authorized_keys` file tampering** by local privileged process.            | Mitigated by A1| File permissions enforced 0o600 by `--generate-keys`. Unauthorized rewrite implies A1 violation; not an additional defense layer.                                                                     |
|T9 | **Audit log post-hoc tampering**.                                            | **Detected, with limits** (S4) | Each run's lines form a hash chain over their exact bytes (`audit.rs::chain_entry`), and after `audit_checkpoint_events` events or `audit_checkpoint_secs` seconds the gateway signs the chain head, bound to the run's random `log_id`, with its SLH-DSA-Shake128f identity key (`checkpoint` lines). `--verify-audit-log` reports a line before the last checkpoint that was edited, removed, inserted or moved; a checkpoint signed for another log or by another key; and a change to the line before a run's first line. Limits: the signing key is a file on the same host (A1), so whoever controls the host can rewrite the log and re-sign it; events after the last checkpoint stay unsigned until the next one; removing the end of the file, its last checkpoint included, cannot be detected from the file alone (copy checkpoints off the host to cover that); a run without a persisted identity is chained but not signed, and a chain without a signature proves nothing, so the verifier reports such runs, runs with no checkpoint and files that start mid-run as not verified (exit 2) rather than OK; rotating with `copytruncate` produces such a file, so rotate by renaming; verification needs `proxy.pub` obtained out of band. Tests: `audit::tests`, `tests/audit_verify_cli.rs`; vectors `tests/vectors/audit-v1.json`. |
|T10| **Nonce reuse, replay, reordering or reflection** of session frames.          | Mitigated since wire `2.1` / `3.2` | Before wire `2.1` / `3.2` this row said Mitigated and was wrong: one AES-256-GCM key (`session_key`) served both directions and both counters started at 0, so a client's first request and the gateway's first response were sealed under the same key and nonce (nonce reuse across directions), and the receiver accepted any nonce. Now the session key is expanded into one key per direction (`crypto.rs::derive_direction_keys`, `docs/KEY-SCHEDULE.md` §5); each direction counts its own nonces from 0 (4 zero bytes ‖ 8-byte big-endian counter, never wraps, exhaustion is an error on both sides); and the receiver accepts only the next expected nonce, so strict receive sequencing also refuses replayed, reordered and reflected frames (`PqSession::decrypt`). Older clients are refused at the hello. Tested in `crypto::tests` and end to end over TCP in `tests/gateway_session.rs`. |
|T11| **DoS** via handshake flood from a single or small set of sources.           | **Pending mitigation** (S7) | `max_connections` + `connection_timeout` provide soft limits today. Planned, not yet tracked in a public issue: per-source rate limiting, a cookie-PoW pre-handshake, and inotify reload of `authorized_keys` for fast revocation. Botnet-class DDoS remains out-of-scope (O3). |
|T12| **Side-channel leaks** in the host OS.                                       | Out of scope (O2)| Memory hygiene is partial. Since 3.0.0 the crate uses `paraxiom-pqc` 0.2.0, whose secret types (ML-KEM decapsulation keys, Falcon and SLH-DSA signing keys, shared secrets) are wiped on drop; in PQTG that covers the long-term signing keys in `PqKeyExchange` and the decapsulation key in `EphemeralKemKey`. PQTG also wipes on drop: the per-direction record keys (`crypto::DirectionKeys`), the v3 key-schedule chain (`kdf::Chain`), the relay's epoch keys and ratchet KEM secrets, and the ETSI 014 key material (`Zeroizing`). Not wiped, among others: the 32-byte copies of the ML-KEM shared secret returned by `encapsulate_to` and `EphemeralKemKey::decapsulate` and held through the handshake (`pqc_secret`), the v2 QKD-mixed secret, the 32-byte handshake `session_key`, the expanded AES key schedules inside `Aes256Gcm` (`aes-gcm` is built without its `zeroize` feature), and the buffers holding an encoded identity while it is saved (`PqKeyExchange::encode`) or loaded (`load_if_present`). Identity keys are stored unencrypted on disk (file mode 0o600). These wiping claims are read from the code and `paraxiom-pqc`'s documentation; this crate has no test that checks them. Beyond that, host hardening is the deployer's responsibility. |
|T13| **Vendor KME compromise** (key generation issues, forged TLS).               | Out of scope (O6)| PQTG cannot distinguish a compromised KME from a working one; it ships whatever the KME delivers.                                                                                                  |

### Status legend

- **Mitigated** — current implementation actively prevents the attack
  (subject to the stated assumptions).
- **Mitigated, argued not proved** — the property holds under the stated
  assumptions but no machine-checked proof exists yet.
- **Detected** — attack succeeds but leaves an evidence trail (signature
  failure, audit anomaly, etc.).
- **Out of scope** — explicitly excluded by §3.

## 5. Properties claimed vs proved

| Property                                            | Status                  | Notes                                                                                                                       |
|-----------------------------------------------------|-------------------------|-----------------------------------------------------------------------------------------------------------------------------|
| ML-KEM-768 key agreement converges                  | **Proved by test**      | `crypto.rs::tests::ml_kem_handshake_produces_matching_shared_secret`                                                        |
| Transcript binds randoms + identities               | **Proved by test**      | `crypto.rs::tests::full_handshake_session_keys_match`, `tampered_transcript_fails_verification`                             |
| No AES-GCM (key, nonce) pair repeats in a session, in either direction; replayed, reordered and reflected frames refused | **Tested**, not proved | `crypto.rs::tests::{client_and_server_first_frames_never_share_a_key_and_nonce, a_frame_reflected_to_its_sender_is_rejected, a_replayed_frame_is_rejected_and_the_stream_survives, an_out_of_order_frame_is_rejected_and_the_stream_survives, both_counters_refuse_to_wrap}` and `tests/gateway_session.rs`; model-based property tests against a reference model (`tests/session_model.rs`, 65,536 cases per variant on 2026-10-15); fuzzing of the frame path (`fuzz/`); symbolic Verifpal models of the record layer, bounded at 3 sessions (`formal/pqtg-gateway-session*.vp`). None of this is a proof; see `formal/GATEWAY-SESSION-RESULTS-2026-10-15.md` for what each run covers. Until wire `2.1` / `3.2` this row read "AES-GCM nonces never repeat under same key: Proved by test" on the strength of `nonce_counter_advances_per_message`, which checks one direction only; across the two directions the claim was false. |
| Sign-and-encrypt round-trip preserves data + signer | **Proved by test**      | `crypto.rs::tests::sign_and_encrypt_roundtrip_with_real_kex`                                                                |
| ETSI 014 v1.1.1 wire format conformance             | **Proved by test**      | `tests/etsi014_emulator.rs` — 9 integration tests against `httpmock` KME                                                    |
| FIPS 203/204/205 parameter conformance              | **Proved by Lean**      | `lean/PQTGProofs/{MLKem,Falcon,Sphincs,Auth,Session,KeyMixing,ETSI014,Handshake}.lean` — 95 lemmas total, zero sorries        |
| EUF-CMA / IND-CCA security of primitives            | **Assumed** (A5–A8)     | Not re-derived in Lean. Inherited from the FIPS standards and assumed of the `paraxiom-pqc` implementation (A10), which has not been externally audited. |
| Forward secrecy under future Falcon SK compromise   | **Argued, not proved**  | Argument: ephemeral ML-KEM keypair per handshake; A5 implies past `kem_ss` is unreachable from any non-handshake key.       |
| Mutual authentication                               | **Server→client only**  | Server signs transcript; clients are authorized by `authorized_keys` lookup but PQTG does not currently challenge the client to prove possession of `dk` for the published `ek`. |

## 6. Known limitations

- **L1** ~~Long-lived signing-key persistence~~ — **resolved**.
  Falcon-512 + SLH-DSA-Shake128f signing keys are persisted to disk via
  `PqKeyExchange::{encode, decode, save, load_if_present}`, atomic
  `tmp + rename` write, 0o600 enforced, secure-permissions check on
  load. `--generate-keys` refuses to overwrite an existing identity.
  Round-trip + truncation + bad-magic + bad-version covered by 6 unit
  tests in `crypto::tests`.
- **L2** Client→server authentication: clients are authorized by vk
  lookup (`authorized_keys`), but no challenge-response (clients are not asked to prove they
  hold the `dk` matching the `ek` they published). Adding this would
  promote "Server→client only" to "Mutual" in §5. The Verifpal model
  (`formal/VERIFICATION-RESULTS-2026-09-12.md`, finding F1) makes the
  gap concrete: with the QKD leg absent or public, an attacker who
  substitutes the client's `kem_ek` in the unauthenticated ClientHello
  obtains the server's session key (the honest client halts on the
  signature; in-session client signatures bound the damage). Tracked as
  backlog B6. Server→client pinning: the server-side enabler
  (`compute_identity_fingerprint` + `--print-fingerprint` +
  `docs/CLIENT-INTEGRATION.md`) has shipped, and
  as of 2026-09-12 the **relay client enforces it**: `relay.pin` is
  required in client mode (`relay.allow_unpinned` is an explicit,
  WARN-logged opt-out), the fingerprint is checked before the signature,
  and a mismatch closes the connection (finding F2, backlog B7). The
  remaining piece is external *gateway* clients performing §2 step 5 of
  `CLIENT-INTEGRATION.md`; the gateway cannot do it for them.
- **L3** No formal proof of forward secrecy (T3). Argued from ephemeral
  ML-KEM but not machine-checked.
- **L4** No DoS mitigation beyond `max_connections` / `connection_timeout`.
- **L5** No protocol-level mechanism for revocation of an authorized vk
  beyond editing the file and restarting.
- **L6** The per-message Falcon signature inside a gateway session
  (`PqSession::sign_and_encrypt`) covers the message data only: no
  session id, no direction, no position. While the record keys are
  secret this costs nothing, because the record layer already binds the
  frame to its session, direction and position. If one direction key
  leaks, it no longer does: an attacker holding `k_c2s` can re-seal a
  request the client really signed at a later position of the same
  session, or into another session whose `k_c2s` it also holds, and the
  gateway accepts it. It still cannot make a request the client never
  signed, and the other direction keeps confidentiality and
  authenticity. Shown on the code by `tests/session_key_leak.rs` and
  symbolically by `formal/pqtg-gateway-session-signed-leak-c2s.vp`
  (`formal/GATEWAY-SESSION-RESULTS-2026-10-15.md`). Closing it means
  signing the session id, direction and counter with the data, which is
  a wire change; not done.

## 7. Review questions for ETSI ISG-QKD

The following are open invitations for working-group feedback:

1. Is the localhost trust boundary (A1, A2) acceptable for the deployment
   profiles ETSI envisions, or should PQTG additionally bracket the
   vendor link with an OS-level mechanism (e.g. UNIX socket only, mTLS
   with a vendor-provided CA, AppArmor/SELinux confinement)?
2. Should `authorized_keys` distribution be standardized (e.g. as a
   companion ETSI specification) or left as deployer's choice?
3. Is "Server→client only" handshake authentication sufficient given
   that clients are still authorized by vk, or should §6 L2 be elevated
   to a blocker before standardization-track adoption?
4. In protocol v3 the hybrid (PQC + QKD, mixed through the keyed chain of
   `docs/KEY-SCHEDULE.md` §4) is used when both are available; protocol v2
   never mixes a QKD key. Is that hybrid composition acceptable, or do
   reviewers want pure QKD or pure PQC depending on deployment posture?

---

*This document is a living artifact and will be updated as the codebase
moves through items (4) and (5) of `TODO.md`. Substantive `ETSI014.lean`
lemmas (item 4) will, where applicable, promote rows in §5 from "Proved
by test" to "Proved by Lean". Reproducible benchmarks (item 5) will
inform §6 L4 (DoS) calibration.*
