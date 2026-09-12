# PQTG Wire Protocol v3 — QKD key-id distribution (design sketch)

Status: **IMPLEMENTED** (2026-08-18, branch feat/protocol-v3-keyid; audited against eprint 2025/1671 — see audit-vs-eprint-2025-1671.md). Originally authored from the
KirQ Site-101 deployment, 2026-06-03.
Supersedes the QKD-mixing portion of `docs/CLIENT-INTEGRATION.md` (v2).

---

## 1. Problem

PQTG v2 derives the session key as

```
session_key = SHA3-256("pqtg-session-v2" ‖ mix_keys(qkd_key, kem_ss) ‖ transcript)
```

where the server (PQTG) pulls `qkd_key` from the KMS via ETSI 014
`enc_keys` during the handshake. **The QKD key — and its `key_ID` — never
appear on the wire.** Consequently:

- The **handshake** (ClientHello/ServerHello, vk-pin, Falcon-512 transcript
  signature, ML-KEM-768 agreement) is fully interoperable. *Verified live
  against the Site-101 gateway.*
- The **post-handshake AES-256-GCM application channel is not** when QKD
  mixing is active: an external client computes `derive_session_key(kem_ss, …)`
  (PQC-only) while the server computes `derive_session_key(mix_keys(qkd, kem_ss), …)`.
  The two keys diverge, so every session frame fails `decrypt_and_verify`.

Observed at deploy time: handshake reaches `Established PQ session` and the
audit log records a real `qkd_key_used` (e.g. `f78fc854-…`), but a client can
never reproduce that secret. v2 is therefore only end-to-end usable in
**PQC-only mode** (KMS unreachable → `mix_keys` reduces to `kem_ss`).

### Why this is the *right* gap to fix, not a bug to delete

The QKD mix is the whole point of PQTG ("hybrid" in the README). Dropping it
would make `qkd_enhanced: true` a lie (see v2 doc §6, "Hybrid-claim spoofing").
The fix is to let both parties **share the same ETSI key the standard way**.

---

## 2. Key idea

ETSI GS QKD 014 already defines two-party key sharing: a **master SAE** calls
`enc_keys` and receives `{key_ID, key}`; the **slave SAE** calls `dec_keys`
with that `key_ID` and receives the *same* `key` bytes from its KME. v3 simply
**transports the `key_ID`** (a non-secret UUID) inside the signed ServerHello so
the client can run the slave side of that exchange itself.

Net effect: the QKD key bytes still never cross the PQTG channel — only the
`key_ID` does — and only a client that can authenticate to a KME *as the
designated slave SAE* can retrieve the bytes.

```
            ┌──────── PQTG @ site 101 (master SAE) ────────┐
client ──►  │ enc_keys(slave = client_sae) → {key_ID, kbytes}│
(slave SAE  │ ServerHello carries key_ID (signed)            │
 @ site N)  └───────────────────────────────────────────────┘
   │
   └─► dec_keys(master = 101, key_IDs=[key_ID]) at its OWN KME → same kbytes
       both sides: mix_keys(kbytes, kem_ss) ⇒ identical session_key
```

This is meaningful only for a **peer-SAE client** (another site with its own
KME that shares keys with Site-101 — the genuine cross-site QKD case). A purely
local client with no KME cannot and should not get QKD bytes over the classical
link; it negotiates **PQC-only** (§5).

---

## 3. Wire changes (Rust struct diffs vs `src/proxy.rs`)

```diff
 pub struct ClientHello {
     pub version: String,              // "3.1" (3.0 = flat labels, not kept)
     pub client_random: [u8; 32],
     pub kem_ek: Vec<u8>,
     pub falcon_vk: Vec<u8>,
     pub slh_dsa_vk: Vec<u8>,
     pub requested_key_size: usize,
+    /// ETSI SAE-ID this client is registered as at its KME. Empty ⇒ no KME,
+    /// request PQC-only. The server allocates the QKD key for this slave SAE.
+    pub client_sae_id: String,
+    /// True iff the client can run ETSI 014 `dec_keys` against a KME that
+    /// shares keys with the server's KME. Drives QKD-vs-PQC negotiation.
+    pub qkd_capable: bool,
+    /// Client clock, seconds since the Unix epoch, under the signature. The
+    /// server refuses a hello more than proxy.hello_max_skew_secs (default
+    /// 120) from its own clock, in either direction (2026-09-12, B8).
+    pub timestamp: u64,
+    /// Falcon-512 signature by the client's identity key (the one falcon_vk
+    /// names) over SHA3-256(D[gateway/v3/client-hello] ‖ len‖client_random
+    /// ‖ len‖timestamp_be_u64 ‖ len‖kem_ek ‖ len‖falcon_vk ‖ len‖slh_dsa_vk
+    /// ‖ len‖requested_key_size_be_u64 ‖ len‖client_sae_id
+    /// ‖ len‖qkd_capable_byte), see docs/KEY-SCHEDULE.md.
+    /// Proof of possession of the allow-listed key, and binds THIS kem_ek to
+    /// it (2026-09-12, closes Verifpal finding F1;
+    /// formal/CLIENTAUTH-RESULTS-2026-09-12.md).
+    pub hello_sig: Vec<u8>,
 }

 pub struct ServerHello {
     pub version: String,              // "3.1"
     pub server_random: [u8; 32],
     pub falcon_vk: Vec<u8>,
     pub slh_dsa_vk: Vec<u8>,
     pub kem_ciphertext: Vec<u8>,
     pub transcript_sig: Vec<u8>,
+    /// Negotiated key mode the server actually used (authoritative).
+    pub key_mode: KeyMode,            // Hybrid | PqcOnly
+    /// Present iff key_mode == Hybrid: the ETSI 014 key_ID (UUID) the client
+    /// must fetch via dec_keys to reproduce the QKD contribution. None in PqcOnly.
+    pub qkd_key_id: Option<String>,
+    /// Master SAE-ID to use in the client's dec_keys call (= PQTG's SAE, e.g. "101").
+    pub master_sae_id: String,
+    /// Bytes of QKD material that were mixed (binds length into the transcript). 0 in PqcOnly.
+    pub qkd_key_len: u32,
 }
+
+#[derive(Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
+pub enum KeyMode { Hybrid, PqcOnly }
```

Framing is unchanged: `[len:u32 BE][bincode struct]`.

---

## 4. Transcript & KDF (bind the key_id under the signature)

The `key_ID` must be covered by the server's Falcon-512 signature so a MITM
cannot substitute a key_id it *can* fetch.

Since wire `3.1` (2026-09-12, backlog B2/B3) every v3 hash and key derivation
uses the domain tree and keyed schedule specified in `docs/KEY-SCHEDULE.md`.
`D[path]` is the 32-byte constant for that path; `len ‖ x` is a big-endian
u32 length prefix followed by `x`, applied to every part, fixed-size ones
included.

```
transcript = SHA3-256(D[gateway/v3/transcript]
                      ‖ len ‖ client_random ‖ len ‖ server_random
                      ‖ len ‖ ek
                      ‖ len ‖ server_falcon_vk
                      ‖ len ‖ ct
                      ‖ len ‖ key_mode_byte                 // 0x01 Hybrid, 0x00 PqcOnly
                      ‖ len ‖ qkd_key_id                    // empty in PqcOnly
                      ‖ len ‖ master_sae_id
                      ‖ len ‖ qkd_key_len_be_u32)           // 0 in PqcOnly

ck          = SHA3-256(D[gateway/v3/chain])
ck          = HMAC-SHA3-256(ck, D[gateway/v3/mix/kem]        ‖ len ‖ kem_ss)
ck          = HMAC-SHA3-256(ck, D[gateway/v3/mix/qkd]        ‖ len ‖ qkd_bytes)   // Hybrid only
ck          = HMAC-SHA3-256(ck, D[gateway/v3/mix/transcript] ‖ len ‖ transcript)
session_key = HMAC-SHA3-256(ck, D[gateway/v3/session-key])
```

Secrets never enter a bare hash: each is mixed through a PRF keyed by the
running chain (`src/kdf.rs::Chain`, `src/crypto.rs::derive_v3_session_key`).
PqcOnly and Hybrid differ by a whole chain step, so no PqcOnly key can equal
a Hybrid key, and the transcript step binds the key to the negotiated mode,
`key_ID`, master SAE-ID and QKD key length. Wire `3.0` used flat labels
(`pqtg-transcript-v3`, `pqtg-session-v3`) and the v2 `mix_keys` combiner; it
is not kept. The v2 schedule (`src/crypto.rs::mix_keys`, `derive_session_key`)
is unchanged, the KirQ Phase 1 client speaks it. Known-answer vectors:
`tests/vectors/handshake-v3.json`, checked by `tests/kdf_kat.rs`.

---

## 5. Negotiation & fallback (no silent downgrade)

```
client_qkd = ClientHello.qkd_capable && !ClientHello.client_sae_id.is_empty()
server_qkd = server policy allows QKD for client_sae_id
             && status(client_sae_id).stored_key_count > 0
             && enc_keys(client_sae_id) succeeds

key_mode = Hybrid  if client_qkd && server_qkd
         = PqcOnly  otherwise
```

The server sets `ServerHello.key_mode` authoritatively and signs it (§4). The
client MUST honor the server's `key_mode`:

- `Hybrid`: client runs `dec_keys` for `qkd_key_id`; if it can't retrieve the
  bytes it **aborts** (does not silently fall back — that would let a MITM force
  PQC-only by stripping the key). Length check: retrieved bytes == `qkd_key_len`.
- `PqcOnly`: client uses `kem_ss` directly.

A client that requires QKD (high-assurance) sets a local policy "refuse
PqcOnly" and aborts if the server negotiates down — the signed `key_mode`
makes that decision tamper-evident.

---

## 6. Handshake sequence (v3, Hybrid)

```
client                              PQTG (master SAE 101)            KMS (via mTLS shim)
  │ ClientHello{v3, client_sae_id=102, qkd_capable=true, hello_sig, …}│
  ├─────────────────────────────────►│                              │
  │                                   │ authorize(falcon_vk,slh_dsa_vk)
  │                                   │ verify hello_sig under falcon_vk (F1)
  │                                   │ status(102) stored_key_count>0│
  │                                   ├─ enc_keys(slave=102) ────────►│
  │                                   │◄── {key_ID, key_bytes} ───────┤
  │                                   │ ss = encapsulate_to(kem_ek)   │
  │                                   │ transcript = …‖key_ID‖…       │
  │                                   │ sig = Falcon.sign(transcript) │
  │ ServerHello{v3, Hybrid, qkd_key_id=key_ID, master_sae_id=101, …} │
  │◄──────────────────────────────────┤                              │
  │ pin-check, verify sig, kem_ss = decap(ct)                        │
  │ dec_keys(master=101, [key_ID]) at client's KME ──► key_bytes      │
  │ session_key = chain(kem_ss, key_bytes, transcript), see §4        │
  │                                   │ session_key = same            │
  │ ===== AES-256-GCM application channel now interoperates =====     │
```

PqcOnly is identical minus the `enc_keys`/`dec_keys` calls and without the
QKD chain step (§4).

---

## 7. Security analysis

- **key_id is not secret.** It's a UUID; possession conveys nothing without
  KME authentication as the slave SAE. Safe to send in clear.
- **Tamper-evidence.** `qkd_key_id`, `key_mode`, `master_sae_id`, `qkd_key_len`
  are all inside the Falcon-512-signed transcript (§4). A MITM cannot swap a
  key_id it can fetch, nor force a downgrade, without breaking the signature
  (and step-5 vk-pinning already prevents substituting the signing key).
- **No QKD bytes on the classical channel** — unchanged from v2's intent.
- **Replay.** `client_random`/`server_random` already randomize the transcript;
  ETSI keys are single-use (KMS `key-expiration.hard`, used-once TTL ≈ 10 s),
  so a replayed `key_id` resolves to an already-consumed/expired key → abort.
- **Downgrade.** Signed `key_mode` + client-side "refuse PqcOnly" policy.
- **DoS.** `enc_keys` runs only *after* authorization (as in v2), so an
  unauthorized peer still cannot make the server consume KMS keys.
- **Client KEM-key binding (2026-09-12).** Authorization alone proves the hello
  *names* an authorized key. `hello_sig` proves the sender *holds* it and bound
  this `kem_ek` to it; the server verifies it after authorization and before
  `enc_keys` / encapsulation, and `respond_v3` re-checks it so the type-state
  cannot yield a session from an unverified hello. Without it an on-path
  attacker presents an authorized client's public keys with its own KEM key
  and, in PqcOnly, obtains the server's session key (Verifpal F1). The
  authenticated model passes both hybrid directions
  (`formal/CLIENTAUTH-RESULTS-2026-09-12.md`).
- **Hello replay (B8, mitigated 2026-09-12).** The hello is one-shot: the
  server contributes no nonce before accepting it, so on the wire a recorded
  honest hello verifies again. No secrecy impact (only the honest client can
  decapsulate), but each replay would cost the server one `enc_keys`
  allocation and one encapsulation. Two server-side checks, run after the
  signature and before any spend: (1) the signed `timestamp` must be within
  `proxy.hello_max_skew_secs` (default 120 s) of the server clock, so a
  recording is worthless after the window; (2) inside the window a bounded
  replay guard (`src/replay.rs`, `proxy.hello_replay_cache_entries`, default
  131072, window = 2 × skew) refuses a `client_random` it has already
  admitted. Only signature-valid, in-window hellos are inserted, so the cache
  cannot be filled without an authorized private key; when full it fails
  closed. Residual: a clock skew larger than the window between an honest
  client and the server refuses that client (a configuration matter, logged).
  This is a stateful mitigation; the symbolic model cannot express it, so the
  Verifpal injectivity query on `hello_sig` stays FAIL by construction.
- **Key schedule (wire `3.1`, 2026-09-12).** Every v3 hash carries a domain
  constant from one tree, and every secret enters the session key through a
  PRF keyed by a running chain rather than a one-shot hash (§4,
  `docs/KEY-SCHEDULE.md`). The change is to constants and keying, not to
  which inputs are bound, so the symbolic results in `formal/` stand
  unchanged; the vectors in `tests/vectors/` tie the models to the code.

---

## 8. Backward compatibility & migration

- `ClientHello.version` negotiates: a v3 server SHOULD accept `"2."` (legacy,
  PQC-only-or-bust per the v2 limitation) and `"3."`. The current check
  `version.starts_with("2.")` in `perform_handshake` becomes
  `starts_with("2.") || starts_with("3.")`, branching on the major.
- bincode is not self-describing: v2 and v3 structs are not mutually
  deserializable, so the version branch MUST pick the struct shape before
  decoding the body. Cleanest: read the frame, peek the leading `version`
  string via a tiny `#[derive(Deserialize)] struct VersionPeek{ version:String }`
  over a prefix, then deserialize the full struct for that major. (bincode
  encodes the `String` first, so a length-bounded peek is reliable.)
- New `docs/CLIENT-INTEGRATION-v3.md` becomes the client contract; v2 doc gains
  a banner pointing here for the QKD-channel caveat.

---

## 9. Implementation touch-points (when promoted from sketch)

| Area | File | Change |
|------|------|--------|
| Structs + `KeyMode` | `src/proxy.rs` | add fields above |
| Negotiation + enc_keys-with-key_id | `src/proxy.rs::perform_handshake` | replace `get_key(32)` with `enc_keys(client_sae_id,…)`, keep the `key_ID`, set `key_mode` |
| Client dec_keys | `src/qkd_client.rs::get_keys_by_id` | **already implemented** (currently `#[allow(dead_code)]`) — reuse verbatim |
| Transcript/KDF labels | `src/crypto.rs::transcript_hash`, `derive_session_key` | v3 labels + extra inputs (new fn variants to keep v2 intact) |
| Per-client slave id | `src/config.rs` | `default_slave_sae_id` becomes a fallback; real value from ClientHello |
| Reference client | `examples/kirq_handshake_client.rs` | add `dec_keys` retrieval + AES-GCM session loop |
| Conformance | `tests/etsi014_emulator.rs` + `test/check-10-v3-hybrid` | add a 10th check: enc/dec round-trip yields equal `mix_keys` inputs |

---

## 10. Open questions

1. **SAE-ID ↔ identity binding.** Today the client's ETSI SAE-ID (KME cert CN)
   is independent of its PQTG Falcon vk. Should `authorized_keys` bind them
   (`… sae=102`) so a client can't claim a slave id it isn't entitled to? The
   server's `enc_keys(slave)` is still gated by KMS policy, but binding closes
   a confused-deputy gap. (Tracks v2 doc's "future revision should bind a SAE_ID
   to a Falcon vk fingerprint.")
2. **Same-site clients.** In the Basejump model `slave_SAE_ID` is a *remote
   site*; a co-located client has no slave key to fetch → always PqcOnly. Worth
   stating explicitly in the client contract so integrators don't expect QKD
   hardening for local callers.
3. **Key size.** KMS serves 256-bit (32-byte) keys only here
   (`status.default.*.key.size.in.bytes=32`); `qkd_key_len` is effectively
   always 32. Keep the field for forward-compat with multi-size KMEs.
4. **Multimodal (`evQ_key_source`).** EvolutionQ's LMC can return MULTIMODAL vs
   QUANTUM keys via `extension_optional`. v3 could surface that in ServerHello so
   the client knows whether its hybrid contribution is ITS-quantum or PQC-LMC.
