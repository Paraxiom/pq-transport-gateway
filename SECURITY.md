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

We follow coordinated disclosure. Because PQTG addresses a known class of vulnerability in ETSI GS QKD 014 (classical TLS on the key delivery interface), we coordinate with affected QKD vendors and standards bodies before public disclosure of any additional findings.

1. Reporter submits privately
2. We acknowledge and investigate
3. We coordinate with affected parties where relevant
4. We develop and test a fix
5. We release the fix and publish an advisory
6. We publicly disclose after users have had reasonable time to update

## Supported versions

| Version | Supported | Notes |
|---|---|---|
| 3.1.x | Yes | Gateway wire `3.2`, and `2.1` only where the operator switches it on; relay `relay-4`. Uses `paraxiom-pqc` 0.2. |
| 3.0.0 | **No** | Wire `2.1` accepted from every listed key, SAE IDs not bound to clients (advisory of 2026-11-12 below). Superseded by 3.1.0, which speaks the same wire versions. |
| 2.0.0 | **No** | Affected by the gateway session nonce reuse (advisory of 2026-10-14 below). Superseded by 3.0.0; do not use. Not wire-compatible with 3.0.0. |
| 1.0.0 | **No** | Yanked. Its handshake did not produce a shared secret. |

Commits on `main` from the initial public release (e3bf242) through e50204d
are affected by the same nonce reuse as 2.0.0.

## Scope

### In scope

- Security of the key delivery protocol (what replaces classical TLS for ETSI GS QKD 014 key delivery)
- KEM negotiation logic
- Authenticated key material delivery
- Session key derivation

### Out of scope

- Vulnerabilities in upstream QKD hardware (report to vendor)
- Classical TLS hole in ETSI GS QKD 014 itself — that is the **motivating threat**, not a PQTG bug. See Zenodo DOI 10.5281/zenodo.18786526

## Security properties

- Written in Rust for memory safety
- Post-quantum algorithms: ML-KEM-768 (FIPS 203) for key encapsulation; Falcon-512 (FN-DSA, FIPS 206, still a draft) for every signature the protocol uses. Clients also present an SLH-DSA-Shake128f (FIPS 205) key, matched against `authorized_keys` and never used to sign or verify
- Designed as a drop-in replacement for the classical TLS layer in ETSI GS QKD 014 deployments

## Lean models

`lean/` holds 111 Lean 4 theorem declarations about abstract models of the
protocol: parameter sizes, handshake structure, session framing, key mixing,
ETSI 014 handling and authentication. They rest on one declared axiom
(`kem_correctness_abstract` in `Handshake.lean`) and contain no `sorry`. They
are not linked to the Rust code, do not prove the security of the
cryptographic schemes, and do not cover the per-direction session keys of
3.0.0. They were not built for this release.

## Known limitations

- Early-stage software despite the 3.x version number: the major version counts wire breaks, not maturity. Use with appropriate caution for production QKD links
- Not yet externally audited
- Assumes trusted QKD hardware upstream; PQTG secures key delivery (the ETSI GS QKD 014 interface). It does not touch the quantum channel, nor the classical channel the two QKD units use between themselves

## Advisories

### 2026-11-12: a signed key request could be replayed on wire 2.1; SAE IDs were not bound to clients

**Affected.** The gateway (`src/proxy.rs`) in `pq-transport-gateway` 3.0.0
and in every commit on `main` through d3ad323. 2.0.0 has the same unsigned
hello and is unsupported for other reasons. The relay (`src/relay.rs`) is
affected by the third point only.

**Issues.**

1. *Wire 2.1.* The 2.1 hello is not signed, the gateway accepted wire 2.1
   from every authorized key, and no setting turned it off. Anyone who knows
   a client's two public keys, which travel in clear in every hello, could
   open a 2.1 session in that client's name. A key request is authenticated
   by the client's Falcon-512 signature over the request bytes only, which
   name no session, time or counter (THREAT-MODEL L6). So one request the
   client had signed, once someone else held its plaintext, was accepted
   again in such a session, and each time the gateway drew a fresh key from
   the key manager and delivered it to the holder of that session. The
   plaintext of a signed request is not public: it takes a leaked direction
   key of one session, a second gateway the client talks to, or the
   client's logs. A request signed in a 3.2 session served as well, because
   one `authorized_keys` line admitted a client on both versions. Shown by a
   test on 3.0.0; in this release,
   `tests/gateway_session.rs::on_wire_2_1_a_signed_request_is_served_again_to_someone_else`
   plays it on a gateway that still lists 2.1.
2. *SAE IDs.* Any authorized client could name any SAE ID in a hybrid
   hello, and the gateway drew a key under that SAE for it. A client could
   use up the keys of another client's SAE. That client then got sessions
   without QKD, which its signed ServerHello told it, and the gateway logged
   a warning only.
3. *Hello replay window.* The replay guard of the wire 3.2 hello, and of
   the relay hello, remembered a hello for one second less than the interval
   in which its timestamp was acceptable. A hello dated exactly the allowed
   skew ahead of the server could be admitted a second time, at the cost of
   one more QKD key and one more encapsulation. No secret was exposed.
4. *No limit per client.* An authorized client could ask for handshakes and
   keys without bound. Each handshake costs a signature by the gateway's
   long-term Falcon-512 key, and each key request one more and a key from
   the key manager.
5. *Input checks.* An SAE ID went into the key manager URL without a check
   of its characters, and the test that the key manager URL is on this
   machine looked for the text "localhost" anywhere in it. From reading the
   code, an authorized client could have steered a request to another path
   of the key manager. This was not tested as an attack.

**Fix.** 3.1.0. Wire 2.1 is off unless `proxy.versions` lists it, and then
serves only keys marked `wire=2.1`, which are refused on 3.2. A client gets
a QKD key only under an SAE ID that its `authorized_keys` line lists
(`sae=`). The replay guard remembers a hello for the whole interval.
Handshakes and key requests are limited per client key and per minute. SAE
IDs are restricted to a safe character set, and the key manager URL is
parsed. When the key manager gives no key, the gateway raises an alarm.

**What stays.** A key marked `wire=2.1`, on a gateway that lists `2.1`, can
still be named by someone else, and a request it signed can still be
replayed, up to that key's limit of key requests per minute. Closing that
means moving the client to wire 3.2. On 3.2 the signature on a request
still covers the request bytes only (L6), which matters if a direction key
leaks.

**Action.** Upgrade the gateway. First read "Before upgrading from 3.0.0"
in `CHANGELOG.md`: a 2.1 client, a hybrid client and a very busy client
each need one setting. Clients themselves need no change.

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
accepted, but does not restore confidentiality, and does not stop content
the peer did sign from being replayed into another position or session,
because it covers the data only (THREAT-MODEL L6). Separately, the receiver
accepted any nonce, so frames could be replayed or reordered within a
session.

**Fix.** Wire `2.1` and `3.2`. The session key is expanded into one key per
direction under distinct, versioned domains (`gateway/v2/key/{c2s,s2c}`,
`gateway/v3/key/{c2s,s2c}`); each direction keeps its own counter from 0 and
never wraps; each end accepts only the next expected nonce, which also refuses
replayed, reordered and reflected frames. The handshakes and their key
schedules are unchanged. Specified in `docs/KEY-SCHEDULE.md` §5, pinned by
`tests/vectors/gateway-session.json`, tested in `src/crypto.rs` and end to end
in `tests/gateway_session.rs`. First release with the fix: 3.0.0.

**Action.** Upgrade the gateway and every client together. A fixed gateway
refuses `2.0`, `3.0` and `3.1` hellos, and a client that follows the updated
§2 step 4 refuses a server answering with an older version, so a mismatch
fails closed rather than falling back. Whether key material delivered in an affected session could be
recovered depends on how much of the frame sealed under the same nonce in the
other direction an observer could predict; handle it under your policy for
possibly exposed keys.
