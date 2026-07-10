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
| A7| SLH-DSA-Shake128f is EUF-CMA secure (FIPS 205).                                     | Forgeable audit-log signatures.                 |
| A8| AES-256-GCM is IND-CCA secure under nonce-respecting use (NIST SP 800-38D).         | Session traffic decryptable / forgeable.        |
| A9| SHA3-256 is collision-resistant and behaves as a random oracle for KDF purposes.    | Transcript collisions / KDF weaknesses.         |
|A10| The audited `paraxiom-pqc` crate correctly implements A5–A8.                        | All cryptographic guarantees collapse.          |

A1 and A2 together define the **localhost trust boundary**.
A5–A9 are inherited; PQTG does not re-derive them.
A10 is a software-supply-chain assumption — `paraxiom-pqc` itself depends
on audited Rust crates (`ml-kem`, `ml-dsa`, `slh-dsa`, `falcon-rs`).

## 3. Scope

### In scope (PQTG defends these)

- **S1** Confidentiality of QKD-delivered key material between vendor KME
  and authorized PQTG clients across the public network.
- **S2** Authentication of clients to PQTG via Falcon-512 + SLH-DSA-Shake128f
  verification keys (`authorized_keys`). *Enforced as of issue
  [#1](https://github.com/Paraxiom/pq-transport-gateway/issues/1) fix:
  unauthorized peers are rejected before any keypair generation,
  fail-closed on empty file. Covered by `auth::tests` (7 unit tests).*
- **S3** Authentication of PQTG to clients via server-side Falcon-512
  signature over the full handshake transcript.
- **S4** Integrity of the audit log via per-entry SLH-DSA-Shake128f
  signature (hash-based, stateless).
- **S5** Forward secrecy of past sessions if the long-term Falcon signing
  key is compromised at a *future* time (achieved via per-handshake
  ephemeral ML-KEM keypair).
- **S6** Mutual binding of session to fresh randomness from both sides
  (`client_random` and `server_random` in the transcript hash).
- **S7** Resistance to handshake flooding from a bounded set of unauthorized
  sources (per-source rate limit + cookie-PoW pre-handshake; see issue
  [#7](https://github.com/Paraxiom/pq-transport-gateway/issues/7)).
  *Status: in-scope as of 2026-05-05; mitigations not yet shipped.*

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
|T6 | **Algorithm downgrade** to weaker primitives.                                | Mitigated      | Algorithms are not negotiated. Protocol version is hard-pinned at v2 in `proxy.rs::PROTOCOL_VERSION`. ML-KEM-768, Falcon-512, SLH-DSA-Shake128f, AES-256-GCM are compile-time constants in `crypto.rs`. |
|T7 | **Harvest-now-decrypt-later** quantum adversary.                             | Mitigated      | All cryptographic primitives are post-quantum (FIPS 203/204/205). No classical KEX (DH/ECDH) anywhere in the wire path. Loopback TLS to the vendor is *out* of scope per O6.                          |
|T8 | **`authorized_keys` file tampering** by local privileged process.            | Mitigated by A1| File permissions enforced 0o600 by `--generate-keys`. Unauthorized rewrite implies A1 violation; not an additional defense layer.                                                                     |
|T9 | **Audit log post-hoc tampering**.                                            | Detected       | Per-entry SLH-DSA-Shake128f signature (hash-based, stateless) over the line content. Tampering invalidates the signature; verification covered by `crypto.rs::tests::slh_dsa_audit_signature_roundtrip`. |
|T10| **Nonce reuse** under same session key.                                      | Mitigated      | AES-GCM nonce is a 4-byte zero prefix concatenated with an 8-byte big-endian session counter (`PqSession::encrypt`). Counter is monotonic and `checked_add(1)`-protected from wrap. Test covers this.  |
|T11| **DoS** via handshake flood from a single or small set of sources.           | **Pending mitigation** (S7) | `max_connections` + `connection_timeout` provide soft limits today. Issue [#7](https://github.com/Paraxiom/pq-transport-gateway/issues/7) tracks per-source rate limiting + cookie-PoW pre-handshake + inotify reload of `authorized_keys` for fast revocation. Botnet-class DDoS remains out-of-scope (O3). |
|T12| **Side-channel leaks** in the host OS.                                       | Out of scope (O2)| `paraxiom-pqc` uses `zeroize` for secret material. Beyond that, host hardening is the deployer's responsibility.                                                                                    |
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
| AES-GCM nonces never repeat under same key          | **Proved by test**      | `crypto.rs::tests::nonce_counter_advances_per_message`                                                                      |
| Sign-and-encrypt round-trip preserves data + signer | **Proved by test**      | `crypto.rs::tests::sign_and_encrypt_roundtrip_with_real_kex`                                                                |
| ETSI 014 v1.1.1 wire format conformance             | **Proved by test**      | `tests/etsi014_emulator.rs` — 9 integration tests against `httpmock` KME                                                    |
| FIPS 203/204/205 parameter conformance              | **Proved by Lean**      | `lean/PQTGProofs/{MLKem,Falcon,Sphincs,Auth,Session,KeyMixing,ETSI014,Handshake}.lean` — 95 lemmas total, zero sorries        |
| EUF-CMA / IND-CCA security of primitives            | **Assumed** (A5–A8)     | Not re-derived in Lean. Inherited from FIPS standards and audited `paraxiom-pqc` crate.                                     |
| Forward secrecy under future Falcon SK compromise   | **Argued, not proved**  | Argument: ephemeral ML-KEM keypair per handshake; A5 implies past `kem_ss` is unreachable from any non-handshake key.       |
| Mutual authentication                               | **Server→client only**  | Server signs transcript; clients are authorized by `authorized_keys` lookup but PQTG does not currently challenge the client to prove possession of `dk` for the published `ek`. |

## 6. Known limitations

- **L1** ~~Long-lived signing-key persistence~~ — **resolved by issue
  [#3](https://github.com/Paraxiom/pq-transport-gateway/issues/3)**.
  Falcon-512 + SLH-DSA-Shake128f signing keys are persisted to disk via
  `PqKeyExchange::{encode, decode, save, load_if_present}`, atomic
  `tmp + rename` write, 0o600 enforced, secure-permissions check on
  load. `--generate-keys` refuses to overwrite an existing identity.
  Round-trip + truncation + bad-magic + bad-version covered by 6 unit
  tests in `crypto::tests`.
- **L2** Client→server authentication: clients are authorized by vk
  lookup (issue [#1](https://github.com/Paraxiom/pq-transport-gateway/issues/1)
  fix), but no challenge-response (clients are not asked to prove they
  hold the `dk` matching the `ek` they published). Adding this would
  promote "Server→client only" to "Mutual" in §5. Server→client
  pinning is now wired (issue
  [#2](https://github.com/Paraxiom/pq-transport-gateway/issues/2)
  partial fix: server-side enabler shipped via
  `compute_identity_fingerprint` + `--print-fingerprint` CLI +
  `docs/CLIENT-INTEGRATION.md`); the remaining piece is each client
  implementation actually performing the pin check.
- **L3** No formal proof of forward secrecy (T3). Argued from ephemeral
  ML-KEM but not machine-checked.
- **L4** No DoS mitigation beyond `max_connections` / `connection_timeout`.
- **L5** No protocol-level mechanism for revocation of an authorized vk
  beyond editing the file and restarting.

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
4. The `mix_keys(qkd, kem_ss)` hybrid (PQC + QKD) is preserved when both
   are available. Is that hybrid composition acceptable, or do reviewers
   want pure QKD or pure PQC depending on deployment posture?

---

*This document is a living artifact and will be updated as the codebase
moves through items (4) and (5) of `TODO.md`. Substantive `ETSI014.lean`
lemmas (item 4) will, where applicable, promote rows in §5 from "Proved
by test" to "Proved by Lean". Reproducible benchmarks (item 5) will
inform §6 L4 (DoS) calibration.*
