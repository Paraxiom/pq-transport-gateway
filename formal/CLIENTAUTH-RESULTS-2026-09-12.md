# Client-authenticated hello: Verifpal results (backlog B6, closes F1)

*2026-09-12. Companion to `formal/VERIFICATION-RESULTS-2026-09-12.md` (the v2 model, M1). Verifpal 1.4.10, same binary, same abstractions. Language kept deliberately unambitious.*

## What changed in the model

`formal/pqtg-handshake-clientauth.vp` is `pqtg-handshake.vp` plus one thing: the client signs its hello with its allow-listed Falcon-512 identity key, and the server verifies that signature before encapsulating (and, in the code, before allocating any QKD key).

```
Client:  hello_sig = SIGN(client_sk, HASH(client_random, kem_ek))
Server:  _ = SIGNVERIF(client_pk, HASH(client_random, kem_ek), hello_sig)?   // then KEM_ENCAP
```

The allow-list is modelled as guarded delivery `Client -> Server: [client_pk]`: the server holds an authentic copy of the authorized client's verification key (`authorized_keys`, distributed out of band); the attacker may read it, not replace it. Server pinning is the guarded `[server_pk]`, as in the base model.

Code mapping (`src/proxy.rs`, branch `feat/v3-client-auth`): `ClientHelloV3.hello_sig` = Falcon-512 over `crypto::client_hello_digest_v3` (label `pqtg-client-hello-v3`, every hello field length-prefixed). Verified in `handshake_v3` after the allow-list check and before the QKD allocation, and again in `respond_v3` so the type-state cannot yield a session from an unverified hello. The model abstracts the digest as `HASH(client_random, kem_ek)`, the two fields an attacker must substitute to mount F1.

## Results

| Model | Queries | 2 sessions | `--saturate` |
|---|---|---|---|
| `pqtg-handshake-clientauth.vp` (QKD key private) | `confidentiality? session_key_s` | **PASS** | unchanged 2→3 |
| | `confidentiality? session_key_c` | **PASS** | unchanged |
| | `authentication? Server -> Client: transcript_sig` | **PASS** | unchanged |
| | `authentication? Client -> Server: hello_sig` | FAIL (replay, see below) | unchanged |
| `pqtg-handshake-clientauth-leak-qkd.vp` (QKD key PUBLIC, the F1 configuration) | `confidentiality? session_key_s` | **PASS** (was FAIL without hello_sig) | unchanged |
| | `confidentiality? session_key_c` | **PASS** (was a tool-artefact FAIL at 2 sessions without hello_sig, F3) | unchanged |
| | `authentication? Server -> Client: transcript_sig` | **PASS** | unchanged |
| | `authentication? Client -> Server: hello_sig` | FAIL (replay) | unchanged |

Outputs: `formal/verifpal-output-clientauth.txt`, `-clientauth-saturate.txt`, `-clientauth-leak-qkd.txt`, `-clientauth-leak-qkd-saturate.txt`.

### F1 is closed

With the QKD key public, the server's session key now holds: the attacker cannot produce `hello_sig` over a substituted `kem_ek`, so the server never encapsulates to an attacker key. This is the "KEM leg carries the session when the QKD leg is broken" direction of the hybrid claim, which the v2 model could not confirm. Both directions of "secure if EITHER leg holds" now hold symbolically for both session keys (the KEM-broken direction was already confirmed in the M1 run).

The F3 artefact (the non-minimized 2-session trace on the client's key) does not appear in the authenticated model: the substitution it relied on is no longer available to the attacker.

### The remaining FAIL is replay, and Verifpal says so itself

> `authentication? Client -> Server: hello_sig reports a duplicate that Server cannot rule out on its own: it contributes nothing to hello_sig before accepting it, so any run of it takes the same message twice. Read it as a replay-protection question about this flight rather than as a forgery.`

The hello is one-shot: the server has contributed no nonce before it accepts the hello, so a recorded honest hello is accepted again in another session. Consequences, stated plainly:

- **No secrecy impact.** A replayed hello makes the server encapsulate to the honest client's `kem_ek`; only the honest client can decapsulate. Both confidentiality queries pass in the presence of this replay.
- **Resource impact (B8).** A replayed hello still makes the server allocate a QKD key for the named SAE and spend a KEM encapsulation. That is the QKD-consumption residual already tracked as B8 (THREAT-MODEL L4). Closing it needs recipient-generated context: a server nonce in a first flight (3-message handshake), or a bounded replay cache of `(falcon_vk, client_random)` within the handshake window. Not done here.

## B8 follow-up (same day): the replay is closed in code, not in the model

The residual above is closed server-side (`src/replay.rs`, `proxy::admit_hello_v3`): the hello now carries a signed `timestamp`, the server refuses anything outside `±proxy.hello_max_skew_secs` (default 120 s) of its clock, and inside that window a bounded replay guard refuses a `client_random` it has already admitted (window = 2 × skew, capacity `proxy.hello_replay_cache_entries`, default 131072, fails closed when full; only signature-valid, in-window hellos are ever inserted). Unit tests cover first sight admitted, replay refused inside the window, the recording refused beyond it by the timestamp, stale/future-dated hellos refused before the guard, invalid signatures refused before both, and the full cache failing closed.

**What the model can and cannot say about it.** Verifpal has no clocks and no server state across sessions, so the `authentication? Client -> Server: hello_sig` query remains FAIL by construction; the model is not re-run for B8 and no query was weakened. The claim is therefore: *symbolically*, both session keys and server authentication hold in both hybrid directions; *operationally*, a recorded hello is refused inside the window by the guard and outside it by the timestamp, so a replay cannot make the server spend a QKD key. Turning that into a proof needs a third flight with a server nonce (recipient-generated context), which is the cleaner protocol and remains the long-term option.

## How to say this

Say: *"With a client-signed hello, the PQTG handshake is symbolically verified (Verifpal 1.4.10, 2 sessions unchanged at 3, under the same assumptions as the M1 run) for session-key confidentiality on both sides and server authentication, in both hybrid directions: QKD key broken, and QKD key public. The client's hello is authenticated but not yet replay-protected; a replay costs the server a QKD key allocation, not any secret."*

Do not say: "mutually authenticated" without the replay caveat, "proven secure", or anything implying the relay handshake (a different protocol) is covered.
