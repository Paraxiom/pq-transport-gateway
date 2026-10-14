# Security Policy

## Reporting a vulnerability

Please do **not** open public GitHub issues for suspected vulnerabilities.

Report privately via one of these channels:

1. **Email:** sylvain@paraxiom.org
2. **GitHub Security Advisories:** use the Security tab of this repository

### What to include

- Description of the vulnerability
- Steps to reproduce
- Potential impact
- Suggested fix (if available)

### Response timeframe

- **Initial acknowledgement:** within 48 hours
- **Status update:** within 7 days
- **Resolution target:** within 30 days for critical issues

### Disclosure process

We follow coordinated disclosure. Because PQTG addresses a known class of vulnerability in ETSI GS QKD 014 (classical TLS on the control channel), we coordinate with affected QKD vendors and standards bodies before public disclosure of any additional findings.

1. Reporter submits privately
2. We acknowledge and investigate
3. We coordinate with affected parties where relevant
4. We develop and test a fix
5. We release the fix and publish an advisory
6. We publicly disclose after users have had reasonable time to update

## Scope

### In scope

- Control-channel protocol security (replacing classical TLS in ETSI 014)
- KEM negotiation logic
- Authenticated key material delivery
- Session key derivation

### Out of scope

- Vulnerabilities in upstream QKD hardware (report to vendor)
- Classical TLS hole in ETSI GS QKD 014 itself — that is the **motivating threat**, not a PQTG bug. See Zenodo DOI 10.5281/zenodo.18786526

## Security properties

- Written in Rust for memory safety
- 99 Lean 4 theorems
- Post-quantum algorithms: ML-KEM-768 (FIPS 203) for key encapsulation; Falcon-512 (FN-DSA, FIPS 206, still a draft) for every signature the protocol uses. Clients also present an SLH-DSA-Shake128f (FIPS 205) key, matched against `authorized_keys` and never used to sign or verify
- Designed as a drop-in replacement for the classical TLS layer in ETSI GS QKD 014 deployments

## Known limitations

- Pre-1.0 software — use with appropriate caution for production QKD links
- Not yet externally audited
- Assumes trusted QKD hardware upstream; PQTG secures the control channel, not the quantum channel itself

## Advisories

### 2026-10-14: gateway session reused AES-GCM nonces across directions

**Affected.** The gateway session layer (`PqSession` in `src/crypto.rs`, used by
`src/proxy.rs`) in `pq-transport-gateway` 2.0.0 and in every commit on `main`
from the initial public release (e3bf242, 2026-07-10) through e50204d: wire
versions `2.0`, `3.0` and `3.1`, and clients written from
`docs/CLIENT-INTEGRATION.md` §2 step 8 as it read before this fix. The relay
(`src/relay.rs`, `relay-4`) is not affected: it already derived one key and
kept one counter per direction, with strict receive sequencing.

**Issue.** One AES-256-GCM key, the handshake's session key, served both
directions, and both ends counted nonces from 0. A client following the
documented step 8 sealed each request under the same key and nonce as the
gateway's response at the same position, starting with the first. Nonce
reuse voids what AES-GCM guarantees for those frames: the XOR of the two
plaintexts is exposed and the GHASH authentication key of the session can be
recovered. Each frame also carries a Falcon-512 signature inside the
encryption, which still stops content the peer did not sign from being
accepted, but does not restore confidentiality. Separately, the receiver
accepted any nonce, so frames could be replayed or reordered within a
session.

**Fix.** Wire `2.1` and `3.2`. The session key is expanded into one key per
direction under distinct, versioned domains (`gateway/v2/key/{c2s,s2c}`,
`gateway/v3/key/{c2s,s2c}`); each direction keeps its own counter from 0 and
never wraps; each end accepts only the next expected nonce, which also refuses
replayed, reordered and reflected frames. The handshakes and their key
schedules are unchanged. Specified in `docs/KEY-SCHEDULE.md` §5, pinned by
`tests/vectors/gateway-session.json`, tested in `src/crypto.rs` and end to end
in `tests/gateway_session.rs`.

**Action.** Upgrade the gateway and every client together. A fixed gateway
refuses `2.0`, `3.0` and `3.1` hellos, and a client that follows the updated
§2 step 4 refuses a server answering with an older version, so a mismatch
fails closed rather than falling back. Whether key material delivered in an affected session could be
recovered depends on how much of the frame sealed under the same nonce in the
other direction an observer could predict; handle it under your policy for
possibly exposed keys.
