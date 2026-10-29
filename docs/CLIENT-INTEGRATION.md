# PQTG Client Integration

This document describes what a PQTG client must implement to interoperate
with the proxy. Aimed at integrators (KirQ engineers, third-party auditors,
anyone porting PQTG into another stack).

It also documents the **vk-pinning protocol** — how
clients verify they're talking to the *legitimate* PQTG server and not
an attacker who has substituted their own Falcon vk.

This repo currently does not ship a reference client. Until one lands,
this doc is the contract. `tests/gateway_session.rs` holds a minimal client
written from it (v2 and v3 handshakes, the session loop of §2.1), run against
a real gateway over TCP.

---

## 1. Wire protocol (v2)

```
ClientHello { version: "2.1", client_random[32], kem_ek, falcon_vk, slh_dsa_vk, requested_key_size }
ServerHello { version: "2.1", server_random[32], falcon_vk, slh_dsa_vk, kem_ciphertext, transcript_sig }
```

Frames are length-prefixed: `[len: u32 BE][bincode-serialized struct]`.
The v3 handshake (wire `"3.2"`) is specified in `PROTOCOL-V3-QKD-KEYID.md`;
its session layer is the one in §2 step 8 and §2.1 below.

Both sides compute:

```
transcript  = SHA3-256("pqtg-transcript-v2"
                       ‖ client_random ‖ server_random
                       ‖ len(ek) ‖ ek
                       ‖ len(falcon_vk) ‖ falcon_vk
                       ‖ len(ct) ‖ ct)

kem_ss      = ML-KEM-768.Decapsulate(client_dk, kem_ciphertext)        (client side)
            = (returned by ML-KEM-768.Encapsulate(client_ek))           (server side)

session_key = SHA3-256("pqtg-session-v2" ‖ kem_ss ‖ transcript)
```

v2 is PQC-only: the gateway never mixes a QKD key into a v2 session, since
v2 cannot tell the client which ETSI 014 key to fetch. Hybrid mode needs v3
(`PROTOCOL-V3-QKD-KEYID.md`).

---

## 2. Required client steps

```
1. Generate ephemeral ML-KEM-768 keypair (ek, dk).        // throw away dk after handshake
2. Generate Falcon-512 + SLH-DSA-Shake128f keypairs.       // long-lived per client
3. Build ClientHello and send.
4. Receive ServerHello. Check ServerHello.version equals the version you
   sent ("2.1", or "3.2" for v3). On mismatch → ABORT: an older gateway
   runs the old session layer (see §2.1), which is not compatible.

5. ▸ VK PINNING ◂
   Compute: server_fp = SHA3-256("pqtg-identity-fingerprint-v1"
                                 ‖ len(falcon_vk) ‖ server_hello.falcon_vk
                                 ‖ len(slh_dsa_vk) ‖ server_hello.slh_dsa_vk)
   Compare against the PINNED fingerprint received out-of-band.
   On mismatch → ABORT, do not derive session_key.

6. Verify server's Falcon-512 signature over the transcript hash.
   On mismatch → ABORT.

7. Decapsulate kem_ciphertext with dk → kem_ss.

8. Derive session_key (§1 for v2; PROTOCOL-V3-QKD-KEYID.md §4 for v3).
   It is NOT an AES key. Expand it into one AES-256-GCM key per
   direction (docs/KEY-SCHEDULE.md §5):

     k_c2s = HMAC-SHA3-256(session_key, D[gateway/v2/key/c2s])
     k_s2c = HMAC-SHA3-256(session_key, D[gateway/v2/key/s2c])

   For "3.2" use D[gateway/v3/key/c2s] and D[gateway/v3/key/s2c].
   The client seals with k_c2s and opens with k_s2c.
   Nonce = 4 zero bytes ‖ 8-byte big-endian counter, one counter per
   direction, each starting at 0.

9. Send and receive length-prefixed encrypted frames per the session
   loop (§2.1).
```

`D[path]` is the 32-byte domain constant of `docs/KEY-SCHEDULE.md` §2; all of
them are published in `tests/vectors/kdf-domains.json`, and
`tests/vectors/gateway-session.json` gives both keys for known session keys
of each version, so a client can be checked byte for byte.

Steps 5 and 6 are independent and both required. Step 5 alone is not
enough (an attacker who somehow obtained the legitimate Falcon vk could
forge step 6); step 6 alone is not enough (the attacker can present
their own legitimate-looking vk-and-signature pair and pass step 6 with
no pin to compare against).

### 2.1 Session loop (wire 2.1 and 3.2)

Every session frame, in both directions:

```
[len: u32 BE][nonce(12) ‖ AES-256-GCM(k_dir, nonce, be32(len(data)) ‖ data ‖ falcon_sig(data))]
```

No associated data. `falcon_sig` is the sender's Falcon-512 signature over
`data`: the client signs with its identity key, the gateway with its own.

```
Client, for each request:
  1. data = bincode(KeyRequest { key_id, size, purpose })
  2. Seal under k_c2s with nonce = 4 zero bytes ‖ be64(send_counter),
     then send_counter += 1. Send the frame.
  3. Read the response frame. Accept it only if its nonce is exactly
     4 zero bytes ‖ be64(recv_counter). Open it under k_s2c; once it
     authenticates, recv_counter += 1. Verify the signature under the
     gateway's pinned Falcon vk. data = bincode(KeyResponse).
  4. Anything else (another nonce, a failed tag, a bad signature):
     close the connection and run a new handshake. Never skip ahead,
     never accept an older counter, never retry under the same counter.
```

- Never seal two frames under the same key and counter. Neither counter
  wraps: the value 2^64 - 1 is never used; reaching it (unreachable in
  practice) means a new handshake.
- TCP keeps order, so each end always knows the next counter to expect;
  a frame with any other nonce is a replay, a reordering or an injection.
- The gateway applies the same rules: it opens under k_c2s, only at its
  next expected counter, so a replayed, reordered or reflected frame ends
  the connection before any key is requested.

Before wire 2.1 and 3.2, step 8 used `session_key` itself as the AES key
in both directions, with both counters starting at 0, so a client's first
request and the gateway's first response were sealed under the same key and
nonce (AES-GCM nonce reuse), and frames were accepted at any nonce. Clients
built on that rule must be updated; the gateway now refuses 2.0, 3.0 and 3.1
hellos.

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
its `/etc/pq-qkd-proxy/authorized_keys` file. Clients
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
| Client skips the fingerprint check (step 5).                            | Vulnerable to TOFU MITM.           |
| Client skips the transcript-signature check (step 6).                   | Server identity not authenticated. |
| Client reuses the ephemeral ML-KEM keypair across handshakes.           | Forward secrecy lost.              |
| Client seals with `session_key` itself, or one key for both directions. | Nonce reuse against the gateway's frames; the gateway refuses the frame.|
| Client accepts a response at any nonce, or not at the next counter.     | Replayed or reordered responses go undetected.|
| Client sends "2.0" or "3.1" in its hello.                               | The gateway refuses the hello.     |
| Client decodes `key` field without checking length matches `key_size/8`.| Vendor-side errors silently absorbed.|
| Client trusts `qkd_enhanced: true` without separately verifying QKD.    | Hybrid-claim spoofing.             |
| Client uses an RNG without an OS entropy source.                        | `client_random` predictability.    |

---

## 7. Versioning

This document tracks wire `2.1` and the session layer it shares with `3.2`;
the v3 handshake itself is specified in `PROTOCOL-V3-QKD-KEYID.md`. The
`version` field in `ClientHello` selects the handshake, by exact match: the
gateway accepts `"2.1"` and `"3.2"` only
(`proxy.rs::handshake_for_version`) and refuses every other version at the
hello, including `"2.0"`, `"3.0"` and `"3.1"`, whose session layer used one key
for both directions.

---

## See also

- `docs/THREAT-MODEL.md` — what the protocol defends and what it doesn't
- `src/crypto.rs::PqKeyExchange` — the canonical reference implementation
- `tests/etsi014_emulator.rs` — example of the ETSI 014 backend behavior
- `benches/handshake.rs` — per-stage performance breakdown
