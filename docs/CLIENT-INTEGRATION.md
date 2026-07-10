# PQTG Client Integration

This document describes what a PQTG client must implement to interoperate
with the proxy. Aimed at integrators (KirQ engineers, third-party auditors,
anyone porting PQTG into another stack).

It also documents the **vk-pinning protocol** that closes issue
[#2](https://github.com/Paraxiom/pq-transport-gateway/issues/2) — how
clients verify they're talking to the *legitimate* PQTG server and not
an attacker who has substituted their own Falcon vk.

This repo currently does not ship a reference client. Until one lands,
this doc is the contract.

---

## 1. Wire protocol (v2)

```
ClientHello { version: "2.0", client_random[32], kem_ek, falcon_vk, slh_dsa_vk, requested_key_size }
ServerHello { version: "2.0", server_random[32], falcon_vk, slh_dsa_vk, kem_ciphertext, transcript_sig }
```

Frames are length-prefixed: `[len: u32 BE][bincode-serialized struct]`.

Both sides compute:

```
transcript  = SHA3-256("pqtg-transcript-v2"
                       ‖ client_random ‖ server_random
                       ‖ len(ek) ‖ ek
                       ‖ len(falcon_vk) ‖ falcon_vk
                       ‖ len(ct) ‖ ct)

kem_ss      = ML-KEM-768.Decapsulate(client_dk, kem_ciphertext)        (client side)
            = (returned by ML-KEM-768.Encapsulate(client_ek))           (server side)

session_key = SHA3-256("pqtg-session-v2" ‖ mix_keys(qkd, kem_ss) ‖ transcript)
```

Where `mix_keys(qkd, kem_ss)` is the SHA3-256-based hybrid combiner if a
QKD key is available; otherwise reduces to `kem_ss` alone.

---

## 2. Required client steps

```
1. Generate ephemeral ML-KEM-768 keypair (ek, dk).        // throw away dk after handshake
2. Generate Falcon-512 + SLH-DSA-Shake128f keypairs.       // long-lived per client
3. Build ClientHello and send.
4. Receive ServerHello.

5. ▸ VK PINNING (issue #2 mitigation) ◂
   Compute: server_fp = SHA3-256("pqtg-identity-fingerprint-v1"
                                 ‖ len(falcon_vk) ‖ server_hello.falcon_vk
                                 ‖ len(slh_dsa_vk) ‖ server_hello.slh_dsa_vk)
   Compare against the PINNED fingerprint received out-of-band.
   On mismatch → ABORT, do not derive session_key.

6. Verify server's Falcon-512 signature over the transcript hash.
   On mismatch → ABORT.

7. Decapsulate kem_ciphertext with dk → kem_ss.

8. Derive session_key. Establish AES-256-GCM with (key=session_key,
   nonce = 4-byte zero prefix ‖ 8-byte u64 counter starting at 0).

9. Send and receive length-prefixed encrypted frames per the session loop.
```

Steps 5 and 6 are independent and both required. Step 5 alone is not
enough (an attacker who somehow obtained the legitimate Falcon vk could
forge step 6); step 6 alone is not enough (the attacker can present
their own legitimate-looking vk-and-signature pair and pass step 6 with
no pin to compare against).

---

## 3. Vk pinning — operator-side

### Generate stable identity (run once on the PQTG host)

```
$ sudo pq-qkd-proxy --generate-keys
Generating PQTG identity (Falcon-512 + SLH-DSA-Shake128f)...
Identity (signing + verify):   /etc/pq-qkd-proxy/proxy.key
Public verify bundle:          /etc/pq-qkd-proxy/proxy.pub
Authorized keys template:      /etc/pq-qkd-proxy/authorized_keys

Identity will be loaded on next startup. Distribute the public
bundle (proxy.pub) to clients out-of-band for vk pinning.
```

### Print the fingerprint for distribution

```
$ pq-qkd-proxy --print-fingerprint
SHA3-256:abcdef0123456789...

Distribute this fingerprint to clients out-of-band.
Clients pin it and reject any handshake whose ServerHello
does not produce a matching SHA3-256 of (falcon_vk || slh_dsa_vk).
```

The fingerprint is **stable across restarts** as long as `proxy.key`
is not regenerated. `--generate-keys` refuses to overwrite an existing
identity precisely so an operator can't accidentally invalidate every
client's pin.

### Distribution channels (operator's choice)

- Signed deployment manifest (most common): include `pqtg_fingerprint =
  "SHA3-256:..."` in a manifest signed by an offline org-root key that
  clients already trust.
- Hardware HSM provisioning: the same HSM that issues the client's own
  long-term keys also signs and delivers the PQTG fingerprint.
- DNS via DNSSEC (DANE-style): `_pqtg.example.com TXT "SHA3-256:..."`
  — out-of-band but discoverable.
- Side-channel announcement: physical handoff, encrypted email, etc.

The pinning protocol is agnostic to the distribution channel; the only
requirement is that the channel itself authenticates the fingerprint.

---

## 4. Vk pinning — client-side reference implementation

```rust
use sha3::{Digest, Sha3_256};

const PINNED: [u8; 32] = /* decoded from SHA3-256:<base64> received
                            out-of-band */;

fn compute_server_fingerprint(falcon_vk: &[u8], slh_dsa_vk: &[u8]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"pqtg-identity-fingerprint-v1");
    h.update((falcon_vk.len() as u32).to_be_bytes());
    h.update(falcon_vk);
    h.update((slh_dsa_vk.len() as u32).to_be_bytes());
    h.update(slh_dsa_vk);
    let mut out = [0u8; 32];
    out.copy_from_slice(&h.finalize());
    out
}

// In your handshake:
let server_fp = compute_server_fingerprint(&server_hello.falcon_vk,
                                           &server_hello.slh_dsa_vk);
if server_fp != PINNED {
    return Err("PQTG identity mismatch — pin violated, possible MITM");
}
```

PQTG's own implementation lives at
`src/crypto.rs::compute_identity_fingerprint` — clients should match it
byte-for-byte to ensure interoperability.

---

## 5. Authorized-keys mechanics (server enforces)

The PQTG server validates the *client's* (`falcon_vk`, `slh_dsa_vk`) against
its `/etc/pq-qkd-proxy/authorized_keys` file (issue
[#1](https://github.com/Paraxiom/pq-transport-gateway/issues/1)). Clients
that aren't in the file are rejected before any keypair generation — this
is fail-closed when the file is empty or missing.

Operators add a client by appending one line:

```
falcon512+slh-dsa-shake128f <base64(falcon_vk_897 ‖ slh_dsa_vk_32)> perm=read,write client@example.com
```

The client must publish the same vk pair in its `ClientHello`.

**Distribution** of these client vks to PQTG operators is symmetric to
operator-fingerprint distribution above (signed manifest, HSM, DNS, etc.).

---

## 6. Common integration mistakes

| Mistake                                                                 | Symptom                            |
|-------------------------------------------------------------------------|------------------------------------|
| Client skips the fingerprint check (step 5).                            | Vulnerable to TOFU MITM (issue #2).|
| Client skips the transcript-signature check (step 6).                   | Server identity not authenticated. |
| Client reuses the ephemeral ML-KEM keypair across handshakes.           | Forward secrecy lost.              |
| Client decodes `key` field without checking length matches `key_size/8`.| Vendor-side errors silently absorbed.|
| Client trusts `qkd_enhanced: true` without separately verifying QKD.    | Hybrid-claim spoofing.             |
| Client uses an RNG without an OS entropy source.                        | `client_random` predictability.    |

---

## 7. Versioning

This document tracks PQTG `0.2.x`. Wire protocol bumps (e.g., to v3 for
issue #8 generalization or issue #7 cookie-PoW) will produce a new
`docs/CLIENT-INTEGRATION-v3.md`. The `version` field in `ClientHello`
allows clients to negotiate; the server rejects unsupported versions
in `proxy.rs::perform_handshake`.

---

## See also

- `docs/THREAT-MODEL.md` — what the protocol defends and what it doesn't
- `src/crypto.rs::PqKeyExchange` — the canonical reference implementation
- `tests/etsi014_emulator.rs` — example of the ETSI 014 backend behavior
- `benches/handshake.rs` — per-stage performance breakdown
