# PQTG — Post-Quantum Transport Gateway

A security gateway that replaces vulnerable classical TLS with post-quantum
cryptography for QKD infrastructure, protecting against quantum computer
attacks on authentication and transport.

📄 **Citation**: S. Cormier, "Residual Classical Vulnerabilities in Quantum
Key Distribution Control Channels," Zenodo, 2026.
DOI: [10.5281/zenodo.18786526](https://doi.org/10.5281/zenodo.18786526).

## The problem

QKD vendors (Toshiba, IDQuantique) use classical TLS for their management
APIs, creating a vulnerability where TLS certificates could be compromised
by quantum computers, allowing attackers to steal quantum keys. This
undermines the quantum security that QKD is supposed to provide.

## The solution

PQTG sits directly on the QKD machine and:

1. Listens only on a quantum-safe port for external clients
2. Authenticates clients via Falcon-512 + SLH-DSA-Shake128f
3. Establishes session keys via **ML-KEM-768** key encapsulation (FIPS 203)
4. Translates inbound requests to the vendor's TLS API on `localhost`
5. Optionally mixes a per-session QKD key into the PQC session key (hybrid)

External access is always post-quantum secure; the vendor's classical TLS
is never exposed beyond the loopback interface.

## Cryptographic stack

PQTG is written entirely in Rust. The post-quantum, AEAD and hash primitives
below go through **[paraxiom-pqc](https://github.com/Paraxiom/paraxiom-pqc)** (pure Rust):

| Layer            | Algorithm                  | Standard       |
|------------------|----------------------------|----------------|
| Key encapsulation| ML-KEM-768                 | FIPS 203       |
| Handshake sig.   | Falcon-512                 | FIPS 206 (pending) |
| Audit-trail sig. | SLH-DSA-Shake128f          | FIPS 205       |
| AEAD             | AES-256-GCM                | NIST SP 800-38D |
| Transcript / KDF | SHA3-256                   | FIPS 202       |

> The classical-TLS client to the vendor's KME (loopback / private VLAN) depends
> on `ring` (C + assembly) for the classical handshake. The network-exposed
> post-quantum channel above is pure Rust; removing `ring` awaits a
> production-grade pure-Rust TLS provider.

## Wire protocol (v2)

```
ClientHello { client_random, kem_ek, falcon_vk, slh_dsa_vk, requested_size }
ServerHello { server_random, falcon_vk, slh_dsa_vk, kem_ciphertext, transcript_sig }

transcript  = SHA3("pqtg-transcript-v2" || cr || sr ||
                   len(ek) || ek || len(vk) || vk || len(ct) || ct)
kem_ss      = ML-KEM-768.Decapsulate(client_dk, kem_ciphertext)        // client
            = ML-KEM-768.Encapsulate(client_ek)                        // server
session_key = SHA3("pqtg-session-v2" || mix_keys(qkd_key, kem_ss) || transcript)
```

If a QKD key is unavailable, `mix_keys` reduces to the PQC secret directly
(PQC-only fallback).

## Installation

```bash
# On your QKD hardware (Toshiba / IDQ / similar)
git clone https://github.com/Paraxiom/pq-transport-gateway
cd pq-transport-gateway
cargo build --release
sudo ./target/release/pq-qkd-proxy --generate-keys
```

## Configuration

Edit `/etc/pq-qkd-proxy/config.toml`:

```toml
[proxy]
listen = "192.168.1.100:8443"

[qkd]
vendor_api  = "https://localhost:443"
vendor_cert = "/etc/qkd/vendor-cert.pem"

[security]
pq_algorithm   = "falcon512"
sig_algorithm  = "slh-dsa-shake128f"
authorized_keys = "/etc/pq-qkd-proxy/authorized_keys"
```

## Authorized keys format

```
falcon512+slh-dsa-shake128f <base64(falcon_vk(897) || slh_dsa_vk(32))> perm=read,write client@example.com
```

## Security properties

- **No external TLS**: vendor TLS stays on `127.0.0.1`
- **PQ-only externally**: every external connection uses Falcon + ML-KEM
- **Hybrid optional**: QKD key, when available, mixed into PQC session key
- **Authenticated key agreement**: server signs the full handshake transcript
- **Forward secrecy**: ephemeral ML-KEM keypair per handshake
- **Audit logging**: every key request signed with SLH-DSA (hash-based, stateless)

## Formal verification

Lean 4 parameter-conformance lemmas live under [`lean/`](lean/). They prove
*size and structural* properties (byte sizes, framing limits, transcript
shape, NTT compatibility, primality of moduli) against the FIPS standards.
They do *not* re-derive cryptographic security from lattice arithmetic;
EUF-CMA / IND-CCA properties are inherited as assumptions from the
respective standards and the audited `paraxiom-pqc` crate.

```bash
cd lean
lake update
lake build
```

## Status

This is `2.0.0`. **`1.0.0` (Feb 2026, on crates.io) is yanked and must
not be used** — it shipped a signature-only "shared secret" function that
did not actually produce a shared secret (each side derived a different
value). `2.0.0` replaces it with real ML-KEM-768 key encapsulation and
re-grounds the handshake on `paraxiom-pqc`. The wire protocol bumped
v1 → v2 and is not backwards compatible.

Despite the `2.0.0` major number, this should still be considered
**pre-stable**: open issues track production gaps including persistence
ergonomics, mutual auth, and DoS hardening. Pin exactly (`= "2.0.0"`)
until those land if you depend on this for anything load-bearing.

## Open-core boundary

The anomaly-detection **method** in `src/anomaly.rs` is public and auditable. The QBER
measurement data it is trained on, and any models derived from it, are proprietary and are
not distributed.

## License

**GPL-3.0-only**, or a **Paraxiom commercial licence**, at your option — see `LICENSE.md`.

Use, study, modify and redistribute freely under GPL-3.0. If you wish to embed this
software in a **proprietary** product without publishing your source, a commercial
licence is required: sylvain@paraxiom.org

Releases published before 8 August 2026 were under `MIT OR Apache-2.0`; that change is
not retroactive.
