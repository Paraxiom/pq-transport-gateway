# PQTG v2 handshake — Verifpal verification results (2026-09-12)

Milestone **M1** of the assurance backlog (B1 in
`docs/NLNET-PROPOSAL-AND-ROSENPASS-BACKLOG-2026-09-12.md`): the symbolic model in
`formal/pqtg-handshake.vp` has now been **executed**, not just written. This
document records the tool, the exact results, every change made to the model,
and the findings, with the language kept deliberately unambitious.

**One-line summary.** Under the model's assumptions (Dolev-Yao active attacker;
two concurrent sessions, verdicts unchanged at three; ML-KEM-768 as Verifpal's
native KEM primitive; SHA3-256 as an ideal `HASH`; the QKD key as a pre-shared
secret; the client *pinning* the server's Falcon key), the PQTG v2 handshake is
**symbolically verified** for session-key confidentiality and server
authentication. The hybrid claim "secure if EITHER leg holds" is **confirmed in
one direction only**: if ML-KEM is broken the QKD key saves the session; if the
QKD key is public, the *server's* session key falls to a real single-session
attack because the handshake does not authenticate the client's KEM key
(THREAT-MODEL.md L2). Nothing here is "proven secure".

---

## 1. Tool, version, install method

| Item | Value |
|---|---|
| Tool | Verifpal 1.4.10 (Nadim Kobeissi / Symbolic Software, GPL-3.0) |
| Binary | `~/.local/bin/verifpal`, Mach-O arm64, no sudo, user-local only |
| Provenance | sha256 of the installed binary `a534243936981d1f513d36b5d42534987a36d1d8561ee5db6f40f0847c6f3130` equals the `verifpal` file inside the official GitHub release archive `verifpal_1.4.10_darwin_arm64.zip` (archive sha256 `026299cd79749feb4f9df1bbd78d6ed18b81d857242b33c6fadaa7a68d7bb6fb`), downloaded from `https://github.com/symbolicsoft/verifpal/releases/download/v1.4.10/`. It is the official release, not a local build. |
| When | The binary was already in place (07:13 today, placed by the preceding session) when this run started; this session verified it rather than reinstalling. |
| Paper | "From Toy to Instrument: Seven Years of Verifpal", https://eprint.iacr.org/2026/1654 |

Two things the old README got wrong, now corrected there:

- `go install verifpal.com/cmd/verifpal@latest` **no longer works**. Verifpal 1.x is
  a Rust crate (the module fetched into `~/go/pkg/mod/verifpal.com@v1.4.10` has a
  `Cargo.toml` and no Go code). Supported routes per upstream: Homebrew tap
  (`brew tap verifpal.com/source https://github.com/symbolicsoft/verifpal && brew install verifpal`),
  the GitHub release zip, or `cargo build --release` (needs Rust ≥ 1.98; this
  machine has cargo 1.96, so the release binary is the practical route here).
- Verifpal 1.x writes public keys as **`PUBKEY(sk)`**, and `G` is a reserved
  word: the classic `G^sk` form is rejected at parse time. The stale
  `verifpal-output-base.txt` that this run replaced was exactly that parse error.

Semantics that matter for reading the verdicts (from `verifpal --help` and the
upstream README): analysis is **bounded** (every principal runs 2 concurrent
sessions by default; `--saturate` climbs to 3 and 4 until verdicts stop
changing). The engine is **sound but incomplete**: a reported attack is meant to
be real, a PASS means "no attack found within the bound". Both caveats turned
out to matter below (§3.2, §4.2).

## 2. Base model — `formal/pqtg-handshake.vp`

Command: `verifpal verify formal/pqtg-handshake.vp` → `formal/verifpal-output-base.txt`
Saturation: `verifpal verify formal/pqtg-handshake.vp --saturate` → `formal/verifpal-output-base-saturate.txt`

| Query | Verdict | Bound | Interpretation |
|---|---|---|---|
| `confidentiality? session_key_s` | **PASS** | search exhausted at 2 sessions; unchanged at 3 | An active attacker cannot compute the server's session key. Note (§3.1): with the QKD key present this holds even though the attacker *can* substitute the client's `kem_ek`; the QKD leg is what keeps the key secret in that branch. |
| `confidentiality? session_key_c` | **PASS** | same | The client's session key stays secret: the only `kem_ct` the client accepts is one the pinned server signed together with the client's own `kem_ek`, `client_random` and `server_random`. |
| `authentication? Server -> Client: transcript_sig` | **PASS** | same | Injective agreement: the signature the client accepts was produced by the server in a matching session. Depends on the pin (§4.1). |

Result code `c0c0a0` at 2 sessions; `--saturate` reports "Verdicts were
unchanged from 2 sessions through 3", result code `c0c0a0`.

The superseded first-cut model with ML-KEM abstracted as `PKE_ENC`/`PKE_DEC`
(`formal/pqtg-handshake-pke-abstraction.vp`) was re-run for comparison and gives
the same `c0c0a0` (`formal/verifpal-output-pke-abstraction.txt`).

## 3. Hybrid property — "secure if EITHER leg holds"

| Variant | File | 1 session | 2 sessions (default) | `--saturate` | Expected by README | Held? |
|---|---|---|---|---|---|---|
| KEM broken (`leaks kem_ss`) | `pqtg-handshake-leak-kem.vp` | — | `c0c0a0` | `c0c0a0` | confidentiality of `session_key_c` holds | **Yes** — both keys and authentication hold. The QKD key in `mix_keys` carries the session. |
| QKD broken (`knows public qkd_key`, both sides) | `pqtg-handshake-leak-qkd.vp` | `c1c0a0` | `c1c1a0` | `c1c1a0` | confidentiality of `session_key_c` holds | **Partly.** `session_key_s` is broken by a real attack (§3.1). `session_key_c` holds at 1 session; the 2-session FAIL is assessed as a tool artifact (§3.2). Authentication holds. |

Outputs: `formal/verifpal-output-leak-kem.txt`, `formal/verifpal-output-leak-qkd.txt`.
Both legs leaked at once was not run (expected to fail; not informative).

### 3.1 Finding F1 — QKD broken ⇒ the server's session key falls (REAL)

Trace (from `verifpal-output-leak-qkd.txt`, identical at 1 session):

```
1.  Attacker constructs PUBKEY(nil).
2.  Attacker replaces kem_ek (sent by Client to Server) with PUBKEY(nil).
3.  Attacker observes KEM_ENCAP(PUBKEY(nil), kem_r)|2 on the wire.          # the ciphertext
4.  Attacker opens it with nil, obtaining KEM_ENCAP(PUBKEY(nil), kem_r)|1.  # the shared secret
5.  Attacker constructs HASH(qkd_key, <shared secret>).                     # mix_keys — qkd_key is public here
6-8. Attacker observes client_random, server_random, server_pk on the wire.
9.  Attacker constructs the transcript HASH(client_random, server_random, PUBKEY(nil), server_pk, kem_ct).
10. Attacker constructs session_key_s = HASH(<mixed>, <transcript>).
```

**Classification: (i) a real protocol observation, not a modeling gap.** The
ClientHello is unauthenticated in the handshake: nothing binds `kem_ek` to the
client's Falcon identity before the server encapsulates to it. An active
attacker can therefore present an authorized client's *public* verification
keys (they pass `authenticator.verify_client`) with its own ML-KEM key, and the
server derives a session key the attacker knows. This is precisely the residual
THREAT-MODEL.md lists as **L2** ("clients are not asked to prove they hold the
`dk` matching the `ek` they published"); Verifpal makes it concrete.

What bounds it in the code as it stands:

- The honest client never completes that handshake: the server's signature covers
  the attacker's `kem_ek`, so the client's `SIGNVERIF` fails and it halts. This
  is a server-side key agreement with an impostor, not a MITM of the client.
- Every in-session request is `decrypt_and_verify`'d under the client's Falcon
  key (`src/crypto.rs::PqSession::decrypt_and_verify`, called from
  `src/proxy.rs::handle_session`), so the impostor cannot issue a `KeyRequest`.
- In the **hybrid** (base) model the same substitution is possible but
  `session_key_s` stays secret because the attacker lacks `qkd_key`. The QKD leg
  is doing that work; the KEM leg alone does not.

A scratch what-if (not saved as a model of record, because the code does not do
it) confirms the obvious remedy: if the client signs `HASH(client_random,
kem_ek)` with its authorized Falcon key and the server checks it before
encapsulating, `session_key_s` holds with `qkd_key` public (`c0c0a0` plus a
replay `a1` on the one-shot hello at 2 sessions, which a server nonce would
close). That is the "promote Server→client to Mutual" item already in
THREAT-MODEL.md §6 L2, now with a symbolic check behind it.

### 3.2 Finding F3 — the 2-session FAIL on `session_key_c` is a tool artifact (TOOL)

At 1 session `session_key_c` **holds** under `knows public qkd_key`. At 2
sessions Verifpal reports a FAIL whose trace it annotates itself:

> Note: these are the substitutions the search recorded; no subset of them was
> confirmed to reproduce the violation on its own, so this trace is not a
> minimized witness.

The trace has the attacker substitute `kem_ek#2` in *session 2*, yet observe
`KEM_ENCAP(PUBKEY(nil), kem_r)` — session 1's randomness, not `kem_r#2` — open it
with its own key to learn `kem_r` (Verifpal models FIPS 203 decapsulation as
recovering the encapsulation randomness, which is correct), then re-encapsulate
to the honest client's `kem_ek` with that same `kem_r` to obtain the client's
shared secret. For that to be a real run, the server would have to have used
the same `kem_r` once toward the attacker's key and once toward the client's.
`generates kem_r` excludes it in the model and fresh randomness per
`kem::encapsulate` excludes it in the code. The two halves of the trace come
from incompatible wire substitutions of the same session; knowledge learned
under one is being reused under the other.

Evidence, in `formal/repro/` (minimal models, each with output):

| Repro (signed ciphertext, pinned signer, unauthenticated `ek`) | 1 session | 2 sessions |
|---|---|---|
| `signed-kem-unauth-ek.vp` (KEM_ENCAP/DECAP) | `c1c0` | `c1c1` |
| `signed-pke-unauth-ek.vp` (PKE_ENC/DEC, server-chosen secret) | `c1c0` | `c1c1` |
| `signed-dh-unauth-ek.vp` (signed ephemeral DH) | `c1c0` | `c1c0` |

`k_s`'s `c1` is the real F1 attack in all three. `k_c`'s 2-session `c1` appears
exactly for the two primitives whose decomposition reveals the server-side
input (`KEM_ENCAP` reveals the seed, `PKE_ENC` reveals the plaintext) and not for
DH, whose `DH_KEX` reveals nothing. The PKE-abstracted PQTG model shows the same
pattern under `knows public qkd_key` (`c1c0a0` at 1 session, `c1c1a0` at 2).

**Consequence, stated plainly:** Verifpal 1.4.10 cannot confirm "ML-KEM alone
protects the *client's* session key" beyond one session for this protocol
shape. I assess the property as true and the 2-session verdict as a false
attack, but the tool does not say so, and this document does not claim the tool
said so. This is worth reporting upstream with `formal/repro/` attached.

## 4. Pin variants — what the guarded `[server_pk]` is buying

The base model delivers `server_pk` guarded: the client has the server's
identity pinned out-of-band. That is the protocol **as specified** in
`docs/CLIENT-INTEGRATION.md` §2 step 5 (compare `SHA3-256(falcon_vk ‖ slh_dsa_vk)`
against the pinned fingerprint). It is **not** what any client in `src/` does
today — see F2. So the assumption was tested by removing the guard.

| Variant | File | 1 session | 2 sessions | `--saturate` |
|---|---|---|---|---|
| No pin (`Server -> Client: server_pk`) | `pqtg-handshake-nopin.vp` | `c0c0a1` | `c0c0a1` | `c0c0a1` |
| No pin AND QKD public | `pqtg-handshake-nopin-leak-qkd.vp` | `c1c0a0` | `c1c1a0` | `c1c1a0` |

### 4.1 Finding F2 — without the pin, server authentication is lost (REAL)

Trace (`verifpal-output-nopin.txt`): the attacker replaces `server_pk` with
`PUBKEY(nil)`, forges a ServerHello (`server_random := nil`, `kem_ct := nil`,
`transcript_sig := SIGN(nil, HASH(client_random, nil, kem_ek, PUBKEY(nil), nil))`)
and the client's `SIGNVERIF` passes because the attacker controls the
verification key. Textbook identity substitution. Confidentiality still reads
`c0c0` in this variant **only because the QKD leg is present**; take it away
(row 2) and both session keys fall.

This is real for:

- `src/relay.rs::client_handshake`, the only client half of a PQTG handshake in
  the repository. It verifies `transcript_sig` against `server_hello.falcon_vk`
  *taken from the wire* and exposes `peer_falcon_vk` "for logging and pinning"
  without anything comparing it to a pin. (The relay also uses a different
  transcript and directional keys and mixes no QKD key, so it is a distinct
  protocol that this model does not cover; a relay-specific model is a follow-up.)
- Any external gateway client that skips CLIENT-INTEGRATION.md §2 step 5.

THREAT-MODEL.md L2 already states "the remaining piece is each client
implementation actually performing the pin check". The model's `[server_pk]` is
therefore a **documented assumption**, stated in the model header, not a
property of the shipped code.

### 4.2 Finding F4 — Verifpal misses the F2 attack when `qkd_key` is public (TOOL)

`pqtg-handshake-nopin-leak-qkd.vp` reports `a0` for the authentication query at
1, 2 and saturated sessions, also when the authentication query is listed
first, and also when it is the **only** query. That contradicts monotonicity:
the attacker in this variant knows strictly more than in `pqtg-handshake-nopin.vp`
(where the same query is `a1`), and the F2 attack does not use `qkd_key` at all.
`VERIFPAL_SOLVE_DEBUG=1` shows the difference: with `qkd_key` private the solver
proposes `server_pk=PUBKEY(nil) ...` and finds the attack; with `qkd_key` public
it emits 94 proposals and never one that substitutes `server_pk`. **Read the
`a0` in that file as a missed attack, not as a pass.** Upstream documents the
engine as incomplete; this is an instance. Also worth reporting.

## 5. Changes made to the model, and why each is still faithful to `src/`

| # | Change | Reason | Fidelity argument |
|---|---|---|---|
| 1 | `server_pk = G^server_sk`, `kem_ek = G^kem_sk` → `PUBKEY(server_sk)`, `PUBKEY(kem_sk)` (made by the preceding session; evidenced by the replaced parse-error output) | Verifpal 1.x syntax; `G` is reserved | Same abstraction (public key derived from a private key), new spelling. Verifpal documents `PUBKEY` as the constructor for signatures *and* KEM encapsulation keys. |
| 2 | `generates kem_ss; kem_ct = PKE_ENC(kem_ek, kem_ss)` / `PKE_DEC(kem_sk, kem_ct)` → `generates kem_r; kem_ss, kem_ct = KEM_ENCAP(kem_ek, kem_r)` / `KEM_DECAP(kem_sk, kem_ct)` | Verifpal 1.4.10 has a native KEM primitive; modelling ML-KEM as PKE with a server-chosen secret was an unnecessary abstraction | `crypto.rs::encapsulate_to` calls `kem::encapsulate(&ek)` and returns `(ct, ss)`: the secret is an *output*, not a chosen plaintext. `kem_r` is ML-KEM's internal encapsulation randomness (fresh per call). `KEM_DECAP` is left unchecked (no `?`) because ML-KEM decapsulation uses implicit rejection and `EphemeralKemKey::decapsulate` only errors on a wrong-length ciphertext. Upstream's own PQXDH example uses the same shape. The PKE version was retained and re-run: identical verdicts. |
| 3 | Header and inline comments rewritten | Record tool version, the pin assumption, and the KEM mapping | No semantic content. |

**Queries were not touched.** No guard was added, no value was made private, no
query was removed or weakened to obtain a pass.

Variants are generated from the base by one-line edits (diffs are in the
variant headers): `leaks kem_ss` after the `KEM_ENCAP` line; `knows private
qkd_key` → `knows public qkd_key` in both principals; `[server_pk]` → `server_pk`.

## 6. Fidelity check against the Rust (what was verified line by line)

| Model | Code | Match |
|---|---|---|
| `Client -> Server: client_random, kem_ek` | `ClientHello { version, client_random, kem_ek, falcon_vk, slh_dsa_vk, requested_key_size }` | Subset: `falcon_vk`/`slh_dsa_vk` (allow-list), `requested_key_size`, `version` omitted as in the README. |
| `kem_ss, kem_ct = KEM_ENCAP(kem_ek, kem_r)` | `encapsulate_to(&client_hello.kem_ek)` → `(kem_ciphertext, pqc_secret)` | Yes |
| `HASH(client_random, server_random, kem_ek, server_pk, kem_ct)` | `transcript_hash(client_random, server_random, kem_ek, server_falcon_pk, kem_ciphertext)` | Same inputs, same order. Label `"pqtg-transcript-v2"` and u32 length prefixes are public constants, not modelled (Verifpal `HASH` takes at most 5 arguments; symbolic terms are already unambiguous). |
| `SIGN(server_sk, transcript_s)` / `SIGNVERIF(server_pk, ...)?` | `host_key.sign_transcript(&transcript)` / `PqKeyExchange::verify_falcon` | Yes; Falcon-512 as an ideal signature. |
| `mixed = HASH(qkd_key, kem_ss)` then `session_key = HASH(mixed, transcript)` | `final_secret = mix_keys(&qkd_key.key_data, &pqc_secret)` then `derive_session_key(&final_secret, &transcript)` (`proxy.rs::perform_handshake`) | Yes: **mix first, then derive**. The module doc comment at the top of `proxy.rs` reads the other way round ("session_key = SHA3(label ‖ kem_ss ‖ transcript) … mixed with it via mix_keys"); the model follows the code, and the comment should be corrected (F5, not in `formal/` scope). |
| `Server -> Client: server_random, kem_ct, transcript_sig` | `ServerHello { version, server_random, falcon_vk, slh_dsa_vk, kem_ciphertext, transcript_sig }` | Subset. Under pinning the wire `falcon_vk` is redundant (the client uses the pinned key); in the nopin variant the wire copy is exactly what the client trusts. |
| `knows private qkd_key` on both sides | `qkd_client.get_key(32)` on the server; the client's retrieval of the *same* key is out of band (ETSI 014) | Assumed. The **no-QKD fallback** (`Err(_) => pqc_secret`, PQC-only, no signal to the client) is not modelled. |

## 7. Findings

| ID | Kind | Finding |
|---|---|---|
| F1 | Protocol (real) | With the QKD leg removed, the server's session key is computable by an attacker who substitutes `kem_ek`: the handshake does not authenticate the client's KEM key (THREAT-MODEL L2). Bounded by in-session client signatures; the QKD leg masks it in the hybrid. Remedy sketch verified in scratch: client-signed ClientHello. |
| F2 | Protocol / deployment (real) | The model's guarded `[server_pk]` assumes the fingerprint pin of CLIENT-INTEGRATION.md §2 step 5. No client in `src/` performs it; `relay::client_handshake` trusts the wire `falcon_vk`. Without the pin, server authentication fails outright and confidentiality rests on the QKD leg alone. |
| F3 | Tool (artifact) | Verifpal 1.4.10 reports a 2-session confidentiality FAIL on the client's key under `knows public qkd_key` that it cannot itself confirm as a witness; it requires server randomness reuse across incompatible substitutions. Holds at 1 session; DH analog unaffected. Minimal repro in `formal/repro/`. |
| F4 | Tool (incompleteness) | Verifpal misses the F2 identity-substitution attack in `pqtg-handshake-nopin-leak-qkd.vp` (`a0` where `a1` is forced by monotonicity); the solver never proposes the `server_pk` substitution once `qkd_key` is public. |
| F5 | Docs nit | `src/proxy.rs` module comment states derive-then-mix; code and model are mix-then-derive. |
| F6 | Code-reading observation (outside the model) | `perform_handshake` fetches and consumes a QKD key (`qkd_client.get_key(32)`) after `verify_client` but before the client has proven possession of anything: the allow-listed verification keys are public, so any peer that copies them can drain QKD key material at handshake rate, bounded only by `max_connections`/timeouts (THREAT-MODEL L4). Not a Verifpal result; noted because it fell out of the fidelity check. |

## 8. How to say this (and how not to)

Say: *"The PQTG v2 handshake has been **symbolically verified** with Verifpal
1.4.10 for session-key confidentiality and server authentication against an
active Dolev-Yao attacker, at two concurrent sessions with verdicts unchanged at
three, under the assumptions that ML-KEM-768 behaves as an ideal KEM, SHA3-256
as an ideal hash, the QKD key is a pre-shared secret, and the client pins the
server's identity. The QKD leg is verified to carry the session when the KEM is
broken. The converse (KEM carries the session when the QKD key is public) holds
for the client's key at one session but **not** for the server's key, because
the handshake does not authenticate the client's KEM key; closing that is a
design item already tracked as L2."*

Do not say: "proven secure", "formally proven", "hybrid security proven in both
directions", or anything implying the unpinned relay client is covered.

## 9. Files written by this run (all under `formal/`)

```
formal/pqtg-handshake.vp                        model of record (native KEM; header documents the pin assumption)
formal/pqtg-handshake-leak-kem.vp               hybrid variant: KEM broken
formal/pqtg-handshake-leak-qkd.vp               hybrid variant: QKD public
formal/pqtg-handshake-nopin.vp                  pin assumption removed
formal/pqtg-handshake-nopin-leak-qkd.vp         pin removed AND QKD public
formal/pqtg-handshake-pke-abstraction.vp        superseded first cut (PKE), kept for comparison
formal/verifpal-output-base.txt                 c0c0a0 (replaces the stale parse-error file)
formal/verifpal-output-base-saturate.txt        c0c0a0, unchanged 2→3 sessions
formal/verifpal-output-leak-kem.txt             c0c0a0
formal/verifpal-output-leak-qkd.txt             c1c1a0 with both traces
formal/verifpal-output-nopin.txt                c0c0a1 with trace
formal/verifpal-output-nopin-leak-qkd.txt       c1c1a0 (a0 is a missed attack, §4.2)
formal/verifpal-output-pke-abstraction.txt      c0c0a0
formal/repro/signed-{kem,pke,dh}-unauth-ek.vp   minimal models for F3, with verifpal-output-*.txt at 1 and 2 sessions
formal/README.md                                updated (install, mapping, results, honest scope)
formal/VERIFICATION-RESULTS-2026-09-12.md       this file
```

Nothing under `src/` was modified. Nothing was committed.

## 10. Next steps

1. **Client authentication in the handshake** (closes F1; THREAT-MODEL L2): have
   the client sign its hello with its authorized Falcon key, with a
   server-supplied nonce if replay matters. Model it as a 3-message variant and
   re-run both hybrid directions.
2. **Pin enforcement** (closes F2): make `relay::client_handshake` and any
   gateway client compare `peer_falcon_vk`/`slh_dsa_vk` against a configured
   fingerprint before `SIGNVERIF`, then the model's guard is a property of the
   code rather than an assumption. Model the relay handshake separately.
3. **Report F3 and F4 upstream** (symbolicsoft/verifpal) with `formal/repro/`.
4. Model the **no-QKD fallback** and a downgrade query; add `freshness?` queries
   (`--auto-queries` is a quick way to see what else the model gives).
5. Longer horizon, unchanged: a computational obligation (CryptoVerif) or a Lean
   protocol-level lemma, to move from "symbolically verified" to "proven".
