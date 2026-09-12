# PQTG formal verification (B1)

**Symbolic** model of the PQTG v2 handshake, in [Verifpal](https://verifpal.com). This is item **B1** of the assurance backlog (`the assurance backlog`) and the headline assurance deliverable: a formally-verified post-quantum handshake *with* a QKD hybrid — a claim the free tools (Rosenpass, PQ-Noise) cannot make, because they have no QKD leg.

**Status (2026-09-12): M1 done — the model has been run, with Verifpal 1.4.10.** Base model: all three queries hold (`c0c0a0`, unchanged from 2 to 3 sessions). The hybrid property holds in the "KEM broken, QKD saves it" direction; the "QKD broken, KEM saves it" direction exposes a real gap on the server side (no client authentication in the handshake, THREAT-MODEL L2) and a Verifpal artifact on the client side. Full results, traces, change log and findings: **`VERIFICATION-RESULTS-2026-09-12.md`**. Read it before quoting any of this.

## What it models
`pqtg-handshake.vp` — the two-message handshake against an **active** (Dolev-Yao) attacker, checking:
1. **session-key confidentiality**, and
2. **server authentication** to the client (explicit, via the Falcon signature over the transcript).

## Mapping to the code (this must stay faithful — update both together)
| Verifpal | PQTG (`src/crypto.rs`, `src/proxy.rs::perform_handshake`) |
|---|---|
| `kem_ek = PUBKEY(kem_sk)` | client's ephemeral ML-KEM-768 encapsulation key (`EphemeralKemKey::new`) |
| `kem_ss, kem_ct = KEM_ENCAP(kem_ek, kem_r)` | `encapsulate_to(client_ek)` → `(ciphertext, shared_secret)`; `kem_r` is ML-KEM's internal encapsulation randomness |
| `KEM_DECAP(kem_sk, kem_ct)` (unchecked) | `EphemeralKemKey::decapsulate` (ML-KEM implicit rejection: never "fails") |
| `SIGN / SIGNVERIF(...)?` | Falcon-512 `sign_transcript` / `verify_falcon`; the `?` halts the client on a bad signature |
| `HASH(client_random, server_random, kem_ek, server_pk, kem_ct)` | `transcript_hash(client_random, server_random, kem_ek, server_falcon_pk, kem_ct)` (same order; the `"pqtg-transcript-v2"` label and length prefixes are public constants, not modelled) |
| `HASH(qkd_key, kem_ss)` | `mix_keys(qkd_key, pqc_secret)` |
| `HASH(mixed, transcript)` | `derive_session_key(final_secret, transcript)` — mix first, then derive, as the code does |
| `knows private qkd_key` (both) | QKD key delivered out-of-band via ETSI-014 (`qkd_client.rs`) |
| `Server -> Client: [server_pk]` (guarded) | server identity fingerprint pinning — **an assumption**: the pin check of `docs/CLIENT-INTEGRATION.md` §2 step 5. No client in `src/` performs it yet (THREAT-MODEL L2); `pqtg-handshake-nopin.vp` is the unpinned case |

Verifpal 1.x syntax notes: public keys are `PUBKEY(sk)` (the old `G^sk` form is rejected — `G` is reserved); `KEM_ENCAP`/`KEM_DECAP` are native, so ML-KEM is no longer abstracted as PKE. The superseded PKE first cut is kept as `pqtg-handshake-pke-abstraction.vp` for comparison; it gives the same verdicts.

## How to run
Verifpal 1.x is a Rust program. `go install verifpal.com/cmd/verifpal@latest` does **not** work any more (the module is a Cargo crate). Use one of:
```
# Homebrew (macOS/Linux)
brew tap verifpal.com/source https://github.com/symbolicsoft/verifpal && brew install verifpal
# or the official release binary (no sudo): https://github.com/symbolicsoft/verifpal/releases  (darwin_arm64 / linux_amd64 ...)
#   unzip, copy `verifpal` to ~/.local/bin, chmod +x
# or from source: cargo build --release   (needs Rust >= 1.98)

verifpal verify formal/pqtg-handshake.vp                 # default: 2 concurrent sessions per principal
verifpal verify formal/pqtg-handshake.vp --saturate      # climb 2 -> 3 -> 4 sessions until verdicts stop changing
verifpal verify formal/pqtg-handshake.vp --result-code --quiet | tail -1   # compact code, e.g. c0c0a0
verifpal verify formal/pqtg-handshake.vp --format html > report.html       # self-contained report with diagrams
```
Result codes: one letter per query in order (`c` confidentiality, `a` authentication), `0` = holds, `1` = attack found. Expected for the base model: **`c0c0a0`**. Saved outputs live next to the models as `verifpal-output-*.txt`.

Verifpal is bounded and **sound but incomplete**: a PASS means "no attack found within the session bound", a reported attack is meant to be real. Both caveats bit in this run (see the results document §3.2 and §4.2): one reported attack is assessed as a false witness (the tool itself flags it as unconfirmed), and one real attack is missed in a variant where monotonicity says it must exist.

## The hybrid property ("secure if EITHER leg holds")
Verifpal can't state "secret if either input is secret" in one query, so it is demonstrated with one-line variants of the base model, each with its saved output:

| Variant | File | Result | Reading |
|---|---|---|---|
| **KEM broken, QKD saves it** (`leaks kem_ss` after `KEM_ENCAP`) | `pqtg-handshake-leak-kem.vp` | `c0c0a0` (2 sessions and saturated) | **Holds.** The QKD key in `mix_keys` protects both session keys. |
| **QKD broken, KEM saves it** (`knows public qkd_key` in both principals) | `pqtg-handshake-leak-qkd.vp` | `c1c0a0` at 1 session, `c1c1a0` at 2 | **Does not fully hold.** `session_key_s` falls to a real attack: the attacker substitutes `kem_ek` (the ClientHello is unauthenticated), so the server shares its key with the attacker — THREAT-MODEL L2, now concrete. `session_key_c` holds at 1 session; the 2-session failure is a tool artifact (randomness reused across incompatible substitutions; minimal repro in `repro/`). |

Both legs leaked at once is expected to fail and was not run.

## The pin assumption
| Variant | File | Result | Reading |
|---|---|---|---|
| No pin (`server_pk` unguarded) | `pqtg-handshake-nopin.vp` | `c0c0a1` | Server authentication is lost (identity substitution); confidentiality survives **only** because of the QKD leg. This is `src/relay.rs::client_handshake` today. |
| No pin and QKD public | `pqtg-handshake-nopin-leak-qkd.vp` | `c1c1a0` | Everything falls. The `a0` is a missed attack by the tool, not a pass. |

## Honest scope of this model (do not oversell)
- **Symbolic, not computational.** Dolev-Yao, bounded sessions. Say "symbolically verified under the model's assumptions," not "proven secure."
- **Primitives are ideal.** ML-KEM-768 as Verifpal's KEM (decapsulation reveals the randomness, as FIPS 203 does), Falcon-512 as an ideal signature, SHA3-256 as an ideal hash.
- **Pinning is assumed, not implemented.** See above and THREAT-MODEL L2.
- **Client authentication is out of scope of the handshake** and the model shows the cost: PQTG authenticates the *server* explicitly (transcript_sig); the *client* is authorized by an allow-list check at ClientHello (`verify_client`) and authenticated per message once the `PqSession` is up (`decrypt_and_verify`). Possession of the KEM key is never proven in the handshake, which is what F1 in the results document exploits when the QKD leg is absent.
- **Omitted:** `falcon_vk`/`slh_dsa_vk` on the wire, `requested_key_size`, `version`, the no-QKD degrade path (`pqc_secret` alone, with no signal to the client), downgrade/version negotiation, the relay handshake (different transcript, directional keys, no QKD mix).

## Next steps
1. ~~M1: install Verifpal, run the base model green, commit the output.~~ Done 2026-09-12 (outputs saved; commit is the user's call).
2. Add **client authentication** to the handshake (sign the hello with the authorized Falcon key, server nonce for replay) and re-run both hybrid directions — closes F1.
3. Enforce the **pin** in `relay::client_handshake` / any gateway client, and model the relay handshake separately — closes F2.
4. Report the two Verifpal issues (F3 artifact, F4 missed attack) upstream with `repro/`.
5. Model the **no-QKD degrade** path and a **downgrade** query; try `--auto-queries` for freshness.
6. Longer horizon: a **computational** obligation (CryptoVerif) or a Lean protocol-level lemma, to move from "symbolically verified" to "proven."

Keep this model in lockstep with `src/crypto.rs`/`src/proxy.rs`: if the handshake changes, the model and this mapping change with it, or the proof is fiction.

## Relay handshake (added 2026-09-12)

The relay (`src/relay.rs`) is a different protocol from the gateway handshake: six-input transcript including the client's Falcon vk, two directional keys, no QKD leg. Its models and results live alongside:

| File | Role |
|---|---|
| `pqtg-relay-handshake.vp` | `relay-1` (superseded): pinned server, unauthenticated client |
| `pqtg-relay-handshake-nopin.vp` | pin removed (`PinPolicy::Unpinned`) |
| `pqtg-relay-handshake-clientauth.vp` | **the shipped relay (`relay-2`)**: server allow-list + client-signed hello (B10, done) |
| `pqtg-relay-handshake-fs.vp`, `-clientauth-fs.vp` | forward secrecy: long-term keys leak in phase 1 |
| `RELAY-RESULTS-2026-09-12.md` | results, findings R1–R4, wording |
| `pqtg-relay-ratchet.vp`, `-leak-k2.vp`, `-leak-k0.vp` | the record-layer hash ratchet (`DirectionalCipher`), three epochs; current-key and early-key leaks |
| `RATCHET-RESULTS-2026-09-12.md` | results, findings T1–T5 (backward secrecy holds, no post-compromise security), wording |

Run: `verifpal verify formal/pqtg-relay-handshake.vp` (add `--sessions 1` or `--saturate`; `--result-code --quiet` for the compact verdict). Expected for `relay-1`: `c1c1c0c0a0a1` at one session (server keys fall to an attacker acting as the client, R1; the honest client's keys and server authentication hold), `c1c1c1c1a0a1` at two (the extra failures are the same tool artefact as gateway F3). Shipped relay (`relay-2`, client-authenticated): `c0c0c0c0a0a0` at one session, only hello replay failing at two; the replay guard in `src/replay.rs` closes that operationally and is outside the symbolic model. Ratchet: `c0c0c0a0a0a0` base; `c0c0c1a0a0a0` with the current key leaked; `c1c1c1a0a0a0` with an early key leaked.
