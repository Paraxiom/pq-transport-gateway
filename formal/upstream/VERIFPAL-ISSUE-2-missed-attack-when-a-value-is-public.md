# Filed upstream on 2026-09-12 as https://github.com/symbolicsoft/verifpal/issues/30

*Body below is what was filed (the attachments section was replaced by links to this branch).*

**Title:** Authentication attack found when a value is `knows private`, missed when the same value is `knows public` (non-monotone verdict)

## Summary

Two models differ only in whether one pre-shared value `qkd_key` is `knows private` or `knows public` on both principals. In the private version Verifpal 1.4.10 finds an identity-substitution attack on `authentication? Server -> Client: transcript_sig` (the server's key is delivered unguarded, the attacker replaces it and signs). In the public version, where the attacker knows strictly more and the attack does not involve `qkd_key` at all, the same query is reported as passing. The verdict should be monotone in attacker knowledge; here it is not. `VERIFPAL_SOLVE_DEBUG=1` shows the solver never proposes the `server_pk` substitution in the public variant (94 proposals, none touching `server_pk`), while it does in the private one. Upstream documents the engine as sound but incomplete; this looks like an instance worth a look because the missed attack is the textbook one.

## Models

Base (attack found), `pqtg-handshake-nopin.vp`:

```verifpal
attacker[active]

principal Server[
    knows private qkd_key
    knows private server_sk
    server_pk = PUBKEY(server_sk)
    generates server_random
]

principal Client[
    knows private qkd_key
    generates client_random
    generates kem_sk
    kem_ek = PUBKEY(kem_sk)
]

Server -> Client: server_pk

Client -> Server: client_random, kem_ek

principal Server[
    generates kem_r
    kem_ss, kem_ct = KEM_ENCAP(kem_ek, kem_r)
    transcript_s = HASH(client_random, server_random, kem_ek, server_pk, kem_ct)
    transcript_sig = SIGN(server_sk, transcript_s)
    mixed_s = HASH(qkd_key, kem_ss)
    session_key_s = HASH(mixed_s, transcript_s)
]

Server -> Client: server_random, kem_ct, transcript_sig

principal Client[
    kem_ss_c = KEM_DECAP(kem_sk, kem_ct)
    transcript_c = HASH(client_random, server_random, kem_ek, server_pk, kem_ct)
    _ = SIGNVERIF(server_pk, transcript_c, transcript_sig)?
    mixed_c = HASH(qkd_key, kem_ss_c)
    session_key_c = HASH(mixed_c, transcript_c)
]

queries[
    confidentiality? session_key_s
    confidentiality? session_key_c
    authentication? Server -> Client: transcript_sig
]
```

Variant (attack missed), `pqtg-handshake-nopin-leak-qkd.vp`: identical except `knows private qkd_key` becomes `knows public qkd_key` in both principals.

## Observed

| Model | `--sessions 1` | 2 sessions | `--saturate` |
|---|---|---|---|
| `knows private qkd_key` | `c0c0a1` | `c0c0a1` | `c0c0a1` |
| `knows public qkd_key` | `c1c0a0` | `c1c1a0` | `c1c1a0` |

In the private model the trace for the `a1` is: attacker replaces `server_pk` with `PUBKEY(nil)`, forges `server_random := nil`, `kem_ct := nil`, `transcript_sig := SIGN(nil, HASH(client_random, nil, kem_ek, PUBKEY(nil), nil))`, and the client's `SIGNVERIF` passes because the attacker controls the verification key. That attack uses nothing about `qkd_key`. Making `qkd_key` public can only add to the attacker's knowledge, yet the verdict flips to `a0`. The confidentiality verdicts in the public variant (`c1…`) do change as expected, so it is specifically the authentication search that stops proposing the substitution.

Also checked: listing the authentication query first, and making it the only query, gives the same `a0`.

## Expected

`a1` in both models (the attack is independent of `qkd_key`), or at least no weaker verdict when the attacker knows more.

## Environment

Verifpal 1.4.10, official release `verifpal_1.4.10_darwin_arm64.zip` (binary sha256 `a534243936981d1f513d36b5d42534987a36d1d8561ee5db6f40f0847c6f3130`), macOS arm64.

## Attachments to include when filing

- `formal/pqtg-handshake-nopin.vp`, `formal/pqtg-handshake-nopin-leak-qkd.vp`, and `verifpal-output-nopin.txt`, `verifpal-output-nopin-leak-qkd.txt`.
- The `VERIFPAL_SOLVE_DEBUG=1` output for both, if the maintainers want it (regenerate; large).

## Context

Same project as the companion report on the non-minimized two-session trace (PQTG, github.com/Paraxiom/pq-transport-gateway, `formal/`). We treat the `a0` here as a missed attack in our own results, not as a pass, and say so in the repository.
