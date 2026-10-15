# PQTG — Technical Specifications

Version target: 2.0.x
Last updated: 2026-05-24

This is the engineering-grade reference for PQTG (Post-Quantum Transport
Gateway). It complements `README.md` (orientation), `docs/THREAT-MODEL.md`
(security assumptions), `docs/CLIENT-INTEGRATION.md` (integration guide),
and `lean/` (formal proofs).

---

## 1. Overview

PQTG is a post-quantum-authenticated proxy that sits in front of an
ETSI GS QKD 014 v1.1.1 endpoint (a QKD vendor server's KME face or a
KMS like EvolutionQ Basejump). It terminates the vendor's classical
TLS on a loopback or private VLAN and exposes only a post-quantum
channel — Falcon-512 + ML-KEM-768 — to external clients.

The product is single-binary, Rust, x86 and ARM (Zynq UltraScale+ via
Yocto). It is **not** a QKD device, **not** a KMS, **not** an HSM, and
**not** an encryptor — it is a control-plane PQ shim.

---

## 2. Architecture

### 2.1 Components

| Component        | Description                                                            |
|------------------|------------------------------------------------------------------------|
| `pqtg` (binary)  | Server: terminates PQ on the external NIC, proxies ETSI 014 to KMS    |
| `qkd_client.rs`  | Library: PQTG's own ETSI 014 client implementation (talks to the KMS) |
| `paraxiom-pqc`   | Crate dependency: FIPS 203/205/206-pending crypto primitives          |

### 2.2 Network topology — two-NIC bump pattern

```
        external network                            KMS (Basejump / vendor KME)
              │                                              │
              │  PQ channel                                  │  classical TLS
              ▼  (Falcon + ML-KEM)                           ▲  (ETSI 014)
       ┌─────────────────────────────────────────────────────┐
       │                 PQTG host                           │
       │   eth0 (external)              eth1 (private VLAN)  │
       │   PQ-only listener   ────────► classical TLS client │
       │                                                     │
       │                      Linux (x86) or Yocto (ARM)     │
       └─────────────────────────────────────────────────────┘
```

Classical TLS is **never** exposed on eth0. Verified by tcpdump per
`docs/THREAT-MODEL.md` claim H4.

### 2.3 PQ handshake protocol

1. Client → PQTG: `ClientHello` with ML-KEM-768 public key, client_random
2. PQTG → Client: `ServerHello` with Falcon-512 signature over
   `(transcript_hash, server_random)`, ML-KEM-768 ciphertext
3. Both sides derive a 32-byte session key from
   `(ml_kem_shared_secret, transcript_hash)`: SHA3-256 over flat labels
   in v2 (`derive_session_key`), an HMAC-SHA3-256 keyed chain in v3
   (`docs/KEY-SCHEDULE.md` §4). No HKDF is used.
4. The session key is expanded by an HMAC-SHA3-256 PRF into one
   AES-256-GCM key per direction, `k_c2s` and `k_s2c`
   (`docs/KEY-SCHEDULE.md` §5); these protect subsequent ETSI 014 calls

Mutual authentication: client-side Falcon identity verified against
`authorized_keys` file before any ETSI 014 forwarding.

### 2.4 ETSI 014 v1.1.1 proxy semantics

PQTG forwards the three spec-mandated endpoints:

| Method | Path                                       | Purpose                     |
|--------|--------------------------------------------|-----------------------------|
| GET    | `/api/v1/keys/{slave_SAE_ID}/status`       | KME status object           |
| GET/POST | `/api/v1/keys/{slave_SAE_ID}/enc_keys`   | Master fetches new keys     |
| GET/POST | `/api/v1/keys/{master_SAE_ID}/dec_keys`  | Slave fetches keys by ID    |

Status object fields (11 required, 1 optional) per spec §5.1.
Key container per spec §5.2 (UUID `key_ID`, base64 `key`).
Error responses per spec §5.3 (`400` / `401` / `503` with structured
`{message, details}` body).

### 2.5 Audit trail

Control-plane events (connection, key request, QKD key use, refused
client) are appended to a JSON-lines log. The entries are not signed: an
SLH-DSA-Shake128f signing path exists (`PqKeyExchange::sign_hash_based`)
but is not wired to the log, and no verification tool ships in this
repository (`docs/THREAT-MODEL.md` S4, T9).

### 2.6 Optional QKD-key-mix (protocol v3 only)

In protocol v3 the key schedule mixes a KMS-supplied QKD key into the
session key through a keyed chain (`docs/KEY-SCHEDULE.md` §4), when the
client asks for it and the KME can supply it. The mode is negotiated per
session and signed by the server (`key_mode`). Mixing through a PRF is
computationally secure; it does not carry over the information-theoretic
security of the QKD key. Protocol v2 never mixes a QKD key.

---

## 3. Cryptographic primitives

| Use                       | Algorithm              | Standard           | Source         |
|---------------------------|------------------------|--------------------|----------------|
| Long-term identity sig    | Falcon-512             | FIPS 206 (pending) | paraxiom-pqc   |
| Ephemeral KEM             | ML-KEM-768             | FIPS 203           | paraxiom-pqc   |
| Second client key (allow-list only, signs nothing) | SLH-DSA-Shake128f | FIPS 205 | paraxiom-pqc |
| Transcript hash           | SHA3-256               | FIPS 202           | sha3 crate     |
| Session key derivation    | SHA3-256 over labels (v2); HMAC-SHA3-256 keyed chain (v3); HMAC-SHA3-256 PRF for the per-direction keys | FIPS 202, RFC 2104 | sha3 + hmac crates; `docs/KEY-SCHEDULE.md` |
| AEAD                      | AES-256-GCM            | NIST SP 800-38D    | aes-gcm crate  |

Falcon-512 signature size: 666 bytes typical.
ML-KEM-768 public key: 1184 bytes; ciphertext: 1088 bytes.
SLH-DSA-Shake128f signature: 7856 bytes.

---

## 4. Configuration

PQTG reads a TOML config file. Reference: `example-config.toml`.

Key parameters:

| Parameter                | Type       | Default        | Notes                                                     |
|--------------------------|------------|----------------|-----------------------------------------------------------|
| `listen.address`         | string     | `0.0.0.0:8443` | PQ listener on the external NIC                           |
| `kms.url`                | string     | —              | Upstream ETSI 014 endpoint (e.g. `https://127.0.0.1:443`) |
| `kms.client_cert`        | path       | —              | Client cert for classical mTLS to KMS                     |
| `kms.client_key`         | path       | —              | Corresponding key                                         |
| `identity.falcon_keypath`| path       | —              | Long-term Falcon-512 signing key (persistent)             |
| `identity.slh_dsa_keypath`| path      | —              | Long-term SLH-DSA-Shake128f audit signing key             |
| `authorized_keys`        | path       | —              | Allowed client Falcon public keys                         |
| `audit.log_path`         | path       | —              | Append-only audit-trail log                               |
| `qkd_mix.enabled`        | bool       | `false`        | Enable QKD-key-mix path                                   |

---

## 5. Hardware targets

| Target                        | Status         | Notes                                                |
|-------------------------------|----------------|------------------------------------------------------|
| x86_64 Linux (Debian/RHEL)    | Supported      | Primary dev target                                   |
| ARM Cortex-A53 (Yocto)        | Expected       | Xilinx Kria KR260, Zynq UltraScale+ MPSoC; untested with paraxiom-pqc 0.2.0 (Falcon needs NEON) |
| ARM64 generic Linux           | Should work    | Untested but no platform-specific code               |
| macOS                         | Dev-only       | Builds and runs; not a deployment target             |

Resource profile (single-instance, moderate load):

- RSS: < 100 MB steady-state
- CPU: bursts to one core during handshake; idle otherwise
- Storage: < 50 MB binary, audit log grows ~1 KB per request
- Network: per-handshake ~3 KB; per-request <500 B + payload

Numbers above are estimates pending the `PERFORMANCE-VALIDATION-PLAN-2026-05-24`
bench (1 week / 1 Kria) for measured values.

---

## 6. Standards compliance

- **ETSI GS QKD 014 v1.1.1** — Key delivery interface. Full endpoint
  coverage (status / enc_keys / dec_keys) with spec-conformant field
  names and error responses. Validated by `tests/etsi014_emulator.rs`
  (9 tests, httpmock-backed).
- **FIPS 203** — ML-KEM (Module-Lattice-based KEM). Via paraxiom-pqc.
- **FIPS 205** — SLH-DSA. Via paraxiom-pqc.
- **FIPS 206 (pending)** — Falcon-512. Via paraxiom-pqc.
- **NIST PQC Round 4** — Falcon-512 (the version implemented).
- **TLS 1.3** — Used for upstream classical TLS to the KMS (vendor-side
  control plane). PQTG does NOT speak TLS 1.3 to external clients —
  external face is PQ-only by design.

---

## 7. What PQTG is NOT

Worth stating explicitly. PQTG does **not**:

- Generate quantum keys (that's the QKD device)
- Encrypt application data (that's the SAE — Nokia 1830 PSI-M, app, HSM)
- Provide key storage at rest (that's HSM — e.g. Crypto4A QxHSM)
- Manage QKD-link physics (that's the QKD vendor server)
- Implement KMS-internal logic (that's the KMS product)
- Provide a QRNG (it consumes randomness from the OS; QRNG-as-source
  is a separate research item)
- Sit in the data path (application traffic flow is unaffected)
- Decrypt QKD-derived keys (those stay opaque to PQTG; PQTG only
  forwards them in the ETSI 014 key container response)

---

## 8. Versioning

Semantic versioning. Wire-format compatibility:

- **Major bump** when the PQ handshake or ETSI 014 surface changes
  (e.g. v2.0.0 broke v1.0.0 by switching to a real ML-KEM-768 KEX —
  v1.0.0 yanked).
- **Minor bump** for backward-compatible feature additions.
- **Patch bump** for bug fixes and non-protocol-breaking improvements.

Current version: `3.0.0` (see `Cargo.toml` and `CHANGELOG.md`). It broke 2.0.0
at the wire (gateway `2.1` / `3.2`) to fix nonce reuse in the gateway session;
2.0.0 is superseded; do not use it.

---

## 9. Security model

See `docs/THREAT-MODEL.md` for the full treatment. Headline:

- **Trust assumptions** A1–A10 (e.g. A1: vendor TLS endpoint is on
  loopback or private VLAN; A2: Falcon long-term signing key is held by
  PQTG only).
- **In scope** S1–S6: external MitM, replay attacks, classical-TLS
  exposure, audit-trail tamper, key-zeroization, forward secrecy.
- **Out of scope** O1–O6: physical-layer QKD attacks, side-channel on
  the host, supply-chain on the binary, DoS-as-availability.
- **Threats** T1–T13 with mitigation and code references.

---

## 10. Known limitations and follow-on

Production-readiness gaps tracked in `TODO.md`:

- **Long-term signing keys regenerated on each start** — `--generate-keys`
  emits a verification bundle but does not yet persist the signing keys
  to disk. Need disk persistence or HSM (Phase 2.3) before production.
- **No HSM integration** — Crypto4A QxHSM integration planned for
  Phase 2.3 of the KirQ roadmap.
- **No multi-host clustering** — single instance only. Horizontal
  scaling is a Phase 3 question.
- **Dead-code warnings** — `EphemeralKemKey`, `verify_slh_dsa`,
  `sign_hash_based` are intentional client-side API surface that the
  current server binary doesn't exercise.

---

## 11. References

| Document                                          | Purpose                                            |
|---------------------------------------------------|----------------------------------------------------|
| `README.md`                                        | Project orientation, getting started               |
| `docs/THREAT-MODEL.md`                             | Trust assumptions and threat catalog               |
| `docs/CLIENT-INTEGRATION.md`                       | How to integrate against PQTG as a client          |
| `docs/QUICK_START.md`                              | Fastest path to a running PQTG                     |
| `docs/VISUAL_GUIDE.md`                             | Visual walkthrough of the architecture             |
| `docs/PERFORMANCE-VALIDATION-PLAN-2026-05-24.md`   | 1-week / 1-Kria perf characterization plan         |
| `docs/kirq/ARCHITECTURE-QKD-CHAIN.md`              | Where PQTG fits in the QKD ↔ KMS ↔ SAE chain       |
| `docs/kirq/TEST-PLAN.md`                           | ETSI 014 conformance test plan                     |
| `docs/kirq/PHASE2-PLAN.md`                         | Multi-phase pilot roadmap                          |
| `lean/PQTGProofs/`                                  | Formal proofs (parameter conformance, protocol shape) |
| `benches/handshake.rs`, `benches/audit.rs`         | Criterion benchmark suites                         |
| `tests/etsi014_emulator.rs`                        | 9 ETSI 014 integration tests against httpmock      |
