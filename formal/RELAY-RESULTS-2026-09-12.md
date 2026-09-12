# PQTG relay handshake: Verifpal results (2026-09-12)

*Companion to `VERIFICATION-RESULTS-2026-09-12.md` (gateway handshake). Same tool (Verifpal 1.4.10, official release binary), same abstractions, same deliberately unambitious language. The relay is a different protocol from the gateway: its own six-input transcript (`relay_transcript`, which includes the client's Falcon vk), two directional keys (`derive_directional_key` with c2s/s2c labels), and no QKD leg.*

**Update, same day:** the relay now ships with client authentication (wire `relay-2`, see *Next* item 1); the "as shipped" rows below describe `relay-1`, and the `client-auth` rows describe what ships now.

**One-line summary.** As `relay-1` shipped, the relay authenticated the **server** to a pinned client and nothing else: the relay server accepts any client (no allow-list, no hello signature), so an attacker can always open a relay session as "the client" and the server-side keys of that session are its own. The pin is load-bearing: without it everything falls, and there is no QKD leg to fall back on. With a client-authenticated hello (the relay twin of the gateway's B6) every confidentiality and server-authentication query holds, and forward secrecy holds symbolically even when both long-term keys leak afterwards.

## Models

| File | What it is |
|---|---|
| `pqtg-relay-handshake.vp` | the relay as shipped: pinned server (`[server_pk]`), unauthenticated client |
| `pqtg-relay-handshake-nopin.vp` | pin removed (the client trusts the wire key), i.e. `PinPolicy::Unpinned` and the pre-2026-09-12 code |
| `pqtg-relay-handshake-clientauth.vp` | fix candidate: server allow-list (`[client_pk]`) + client-signed hello, verified before encapsulation |
| `pqtg-relay-handshake-fs.vp` | as shipped, then `leaks server_sk` in phase 1 |
| `pqtg-relay-handshake-clientauth-fs.vp` | client-authenticated, then BOTH `server_sk` and `client_sk` leak in phase 1 |

Modelling notes: Verifpal `HASH` takes at most five arguments and `relay_transcript` has six, so the transcript is nested `HASH(HASH(client_random, server_random, kem_ek), kem_ct, client_pk, server_pk)`; symbolically equivalent. The directional labels are public constants. `slh_dsa_vk` and the version string are public constants and omitted. The code's length checks are not modelled.

## Results (result codes: one `c`/`a` per query in file order, 0 = pass, 1 = fail)

| Model | queries | 1 session | 2 sessions | `--saturate` |
|---|---|---|---|---|
| as shipped | `key_s2c_s, key_c2s_s, key_c2s_c, key_s2c_c, auth S→C, auth C→S` | `c1c1c0c0a0a1` | `c1c1c1c1a0a1` | unchanged 2→3 |
| no pin | same | `c1c1c1c1a1a1` | `c1c1c1c1a1a1` | (not run; already total) |
| client-auth | `…, auth S→C, auth C→S(hello_sig)` | `c0c0c0c0a0a0` | `c0c0c0c0a0a1` | unchanged 2→3 |
| fs (as shipped + server_sk leak) | `key_c2s_c, key_s2c_c, auth S→C` | `c0c0a0` | `c1c1a0` | (inherits the artefact below) |
| client-auth fs (both keys leak) | four keys + auth S→C | `c0c0c0c0a0` | `c0c0c0c0a0` | unchanged 2→3 |

Outputs: `verifpal-output-relay-handshake*.txt` (one per model, plus `-1session` and `-saturate` where run).

## Findings

### R1 (real, design): the relay server does not authenticate its client
`src/relay.rs::server_handshake` accepts any `RelayHello`: the client's `falcon_vk` is carried, length-checked, hashed into the transcript, and checked against nothing (`RelaySession::peer_falcon_vk` is "for logging and pinning"); the hello is signed by nobody. In the model the attacker replaces `kem_ek` (and `client_pk`) with its own and the server's two directional keys are the attacker's: `key_s2c_s`, `key_c2s_s` fail at one session with a minimized trace, and `authentication? Client -> Server: kem_ek` fails. This is not an attack on an honest client's session (see R3); it is the statement that **anyone who can reach a relay server port can open a post-quantum tunnel to its backend**. What bounds it today: in the QuantumHarmony deployment the backend is a validator's p2p port and libp2p's `--reserved-only` peer-id check is the actual gate; the relay server's per-source connection cap and handshake timeout bound the cost of a stranger's handshake. For any other backend the relay is an open door. **Fix = the relay twin of B6 + the mirror of `ServerPin`:** an allow-list of client fingerprints on the server (`relay.authorized_clients`) and a client-signed hello verified before encapsulation. The `clientauth` model shows exactly that closes it. Tracked as backlog **B10**.

### R2 (real, confirmed): the pin is load-bearing, with nothing behind it
Remove the pin and every query fails at one session: the attacker substitutes `server_pk`, forges the ServerHello, and both sides' keys are its own. The gateway had a QKD leg that kept confidentiality when the pin was absent (gateway F2, `c0c0a1`); the relay has none, so unpinned relay = plaintext-equivalent against an on-path attacker. This is what B7 (`relay.pin` required, `PinPolicy::Unpinned` explicit and WARN-logged) closed on 2026-09-12.

### R3 (tool artefact, same as gateway F3): the 2-session FAIL on the honest client's keys
At one session the honest client's `key_c2s_c`/`key_s2c_c` hold under the pin. At two sessions they fail with the trace Verifpal itself marks "not a minimized witness": the attacker substitutes `kem_ek#2` in session 2, opens the encapsulation to its own key to learn `kem_r`, then re-encapsulates to the honest `kem_ek` with that same `kem_r`. That requires the server to use one `kem_r` toward two different keys; `generates kem_r` excludes it in the model and fresh randomness per `kem::encapsulate` excludes it in the code. Identical pattern to `VERIFICATION-RESULTS-2026-09-12.md` §3.2 and `formal/repro/`; it disappears in the client-authenticated model, where the substitution is no longer available. Same upstream report: [symbolicsoft/verifpal#29](https://github.com/symbolicsoft/verifpal/issues/29).

### R4 (holds, symbolically): forward secrecy
With the server's long-term key leaked after the handshake, the honest client's keys stay confidential at one session (`c0c0a0`); the two-session run inherits R3. On the client-authenticated model, with **both** long-term keys leaked afterwards, all four directional keys stay confidential at two sessions, unchanged at three. That is THREAT-MODEL T3/S5 ("argued, not proved") now symbolically checked for the relay: the session secret comes from an ephemeral ML-KEM key pair and the Falcon keys only ever sign.

## How to say this

Say: *"The relay handshake is symbolically verified (Verifpal 1.4.10) for server authentication to a pinned client and, at one session, for the confidentiality of the pinned client's keys; the relay server does not authenticate its clients (by design today, gated by libp2p in the QuantumHarmony deployment), which a client-signed hello with a server-side allow-list closes in the model. Forward secrecy against later loss of both identity keys holds symbolically for the authenticated variant."*

Do not say: "mutually authenticated relay", "proven secure", or that an unpinned relay client is protected by anything.

## Next
1. ~~**B10**: implement relay client authentication~~ **Done the same day (wire `relay-2`).** `src/relay.rs`: `ClientPolicy::Authorized(fingerprints)` on the server (`relay.authorized_clients`, `--client`), a signed and time-stamped `RelayHello`, and a replay guard (`src/replay.rs`, window 2 × 120 s) checked in the order allow-list → signature → freshness → first sight, before encapsulation. `ClientPolicy::AnyClient` (`relay.allow_any_client`, `--any-client`) is the explicit, WARN-logged opt-out. **`pqtg-relay-handshake-clientauth.vp` is now the model of the shipped relay**; `pqtg-relay-handshake.vp` documents `relay-1`. The replay guard is stateful and outside the symbolic model, so the `hello_sig` injectivity query stays FAIL by construction, as for the gateway (`CLIENTAUTH-RESULTS-2026-09-12.md`).
2. Report R3 upstream together with gateway F3 (same pattern, second protocol; B9, drafted in `formal/upstream/`).
3. Model the ratchet (`DirectionalCipher` epochs) separately; nothing here covers it.
