# Draft issue for symbolicsoft/verifpal (not filed yet)

**Title:** Two-session confidentiality FAIL whose trace reuses one `KEM_ENCAP` randomness across incompatible substitutions; the tool itself marks it "not a minimized witness"

## Summary

On a small signed-KEM protocol (server signs `HASH(ek, ct)` with a pinned key, the client's `ek` is unauthenticated), Verifpal 1.4.10 reports the client's derived key as compromised at 2 sessions but not at 1. The attack trace it prints requires the server to have used the same encapsulation randomness `r` once toward the attacker's key and once toward the honest client's key, which `generates r` excludes. The trace is annotated by Verifpal as "not a minimized witness". The same pattern appears with `PKE_ENC`/`PKE_DEC` (server-chosen secret) and does not appear with `DH_KEX`. I think this is a false attack produced by combining knowledge across two mutually exclusive substitutions of the same session; reporting it in case it is useful.

## Minimal model

```verifpal
// signed-kem-unauth-ek.vp
attacker[active]
principal Server[ knows private ssk
  spk = PUBKEY(ssk) ]
principal Client[ generates dk
  ek = PUBKEY(dk) ]
Server -> Client: [spk]
Client -> Server: ek
principal Server[ generates r
  ss, ct = KEM_ENCAP(ek, r)
  sig = SIGN(ssk, HASH(ek, ct))
  k_s = HASH(ss) ]
Server -> Client: ct, sig
principal Client[ ss_c = KEM_DECAP(dk, ct)
  _ = SIGNVERIF(spk, HASH(ek, ct), sig)?
  k_c = HASH(ss_c) ]
queries[ confidentiality? k_s
  confidentiality? k_c ]
```

## Observed

| Model | `--sessions 1` | default (2 sessions) |
|---|---|---|
| `signed-kem-unauth-ek.vp` (above) | `c1c0` | `c1c1` |
| same with `PKE_ENC(ek, s)` / `PKE_DEC(dk, ct)` and a server-generated `s` | `c1c0` | `c1c1` |
| same with signed ephemeral DH (`DH_KEX`) | `c1c0` | `c1c0` |

`k_s` failing is expected and real: `ek` is unauthenticated, the attacker substitutes it, the server encapsulates to the attacker. `k_c` is the question. The client only accepts a `ct` whose signature covers the client's own `ek`, so in one session the attacker cannot make the client decapsulate an attacker-chosen ciphertext, and Verifpal agrees at 1 session.

At 2 sessions the trace for `k_c` (abridged; the full text is attached) is:

1. attacker replaces `ek#2` (session 2) with `PUBKEY(nil)`;
2. attacker observes `KEM_ENCAP(PUBKEY(nil), r)|2` on the wire, i.e. a ciphertext made with **session 1's** `r`, not `r#2`;
3. attacker opens it with `nil`, "obtaining `r`";
4. attacker constructs `KEM_ENCAP(PUBKEY(dk), r)|1`, session 1's honest shared secret, by re-encapsulating to the honest `ek = PUBKEY(dk)` with that same `r`;
5. derives session 1's `k_c`.

followed by the tool's own note:

> Note: these are the substitutions the search recorded; no subset of them was confirmed to reproduce the violation on its own, so this trace is not a minimized witness.

For step 2 to be a real run, the server would have to have encapsulated with session 1's `r` toward the attacker's key, which only happens if session 1's `ek` was substituted; but the derived `k_c` in step 5 is session 1's honest key, which requires session 1's `ek` **not** to have been substituted. The two halves of the trace come from incompatible wire substitutions of the same session, and knowledge learned under one is reused under the other. That `KEM_ENCAP`/`PKE_ENC` show it and `DH_KEX` does not fits: those two primitives' decomposition reveals the server-side input (`r`, resp. the plaintext), DH's does not.

## Expected

Either `k_c` holds at 2 sessions as it does at 1, or a minimized witness that is a valid run.

## Environment

Verifpal 1.4.10, official release `verifpal_1.4.10_darwin_arm64.zip` (binary sha256 `a534243936981d1f513d36b5d42534987a36d1d8561ee5db6f40f0847c6f3130`), macOS arm64. Commands: `verifpal verify signed-kem-unauth-ek.vp --sessions 1` and `verifpal verify signed-kem-unauth-ek.vp`.

## Attachments to include when filing

- `formal/repro/signed-kem-unauth-ek.vp`, `signed-pke-unauth-ek.vp`, `signed-dh-unauth-ek.vp` and their `verifpal-output-*.txt`.
- The full-protocol instance where we first saw it: `formal/pqtg-handshake-leak-qkd.vp` / `verifpal-output-leak-qkd.txt` (a KEM + signature + pre-shared-key handshake; same trace shape on `session_key_c`), and `formal/pqtg-relay-handshake.vp` / `verifpal-output-relay-handshake.txt` (a second protocol, same shape on the honest client's keys).

## Context, for the maintainers' interest

Both protocols are from PQTG (github.com/Paraxiom/pq-transport-gateway, GPL-3.0), a post-quantum transport gateway; the models and results are in the repository under `formal/`. Verifpal has been genuinely useful: the same runs found two real design gaps (an unauthenticated client KEM key, and an unpinned server key) that are now fixed. This report is the one place where we believe the tool's answer is not a valid run. Happy to test a fix.
