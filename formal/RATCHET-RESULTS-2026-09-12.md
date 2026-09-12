# PQTG relay record layer (the silent ratchet): Verifpal results (2026-09-12)

*Companion to `RELAY-RESULTS-2026-09-12.md` (handshake). Same tool (Verifpal 1.4.10), same conventions. Covers `src/relay.rs::DirectionalCipher`: the per-direction AES-256-GCM record layer whose key advances by a one-way hash every `REKEY_EVERY_RECORDS` records with nothing on the wire.*

**One-line summary.** The record layer is symbolically verified for confidentiality and injective authentication of every record across three epochs, and the ratchet gives exactly what the code says and no more: a key recovered in epoch N does not yield epochs before N (backward secrecy), and it does yield every epoch after N (no post-compromise security), because the chain is a deterministic hash with no fresh entropy.

## What the model is

`pqtg-relay-ratchet.vp`, one direction, three epochs unrolled, one record per epoch:

| Code (`src/relay.rs`) | Model |
|---|---|
| directional key from the handshake | `k0 = HASH(lbl, ss)`, `ss` from an ephemeral KEM whose `ek` and `ct` are delivered guarded (stand-in for the signed, pinned, allow-listed handshake proven in `pqtg-relay-handshake-clientauth.vp`); fresh per session |
| `maybe_ratchet`: `k(n+1) = SHA3-256(RATCHET_LABEL ‖ k(n) ‖ n+1)` | `k1 = HASH(lbl, k0, e1)`, `k2 = HASH(lbl, k1, e2)` |
| `seal`: `nonce = epoch ‖ counter`, AES-256-GCM, no associated data | `AEAD_ENC(k_epoch, n_epoch, m, nil)` (Verifpal 1.4.10 signature: key, nonce, plaintext, ad) |
| `open`: exact next nonce required, then authenticated decryption | `AEAD_DEC(k_epoch, n_epoch, c, nil)?` |
| both sides ratchet at the same count, nothing exchanged | both principals derive `k1`, `k2` independently |

Modelling notes. Verifpal 1.x reasons about AEAD nonce reuse under a shared key across parallel sessions, so the directional key had to be fresh per session (as it is in the code: one handshake per connection); a `knows private k0` shared constant would have produced a spurious cross-session nonce-reuse attack. Within a session the three nonces are distinct public constants, which is what `epoch ‖ counter` guarantees. The other direction is the same model under the other key. Ratchet timing (the record count) is not modelled; it is a counter both sides own.

## Results (one `c`/`a` per query in file order: `m0 m1 m2 c0 c1 c2`)

| Model | 1 session | 2 sessions | `--saturate` |
|---|---|---|---|
| `pqtg-relay-ratchet.vp` | `c0c0c0a0a0a0` | `c0c0c0a0a0a0` | unchanged 2→3, all pass |
| `-leak-k2.vp` (current epoch key leaks after the run) | `c0c0c1a0a0a0` | `c0c0c1a0a0a0` | (not run) |
| `-leak-k0.vp` (an early epoch key leaks after the run) | `c1c1c1a0a0a0` | `c1c1c1a0a0a0` | (not run) |

Outputs: `verifpal-output-relay-ratchet*.txt`.

## Findings

### T1 (holds): every record is confidential and injectively authenticated
No substitution and no replay of a record into another epoch's slot, at one, two and three sessions. The per-epoch key plus the nonce bound into the AEAD is what the receiver's strict `open()` sequencing relies on, and the model confirms the cryptographic side of it.

### T2 (holds): backward secrecy, exactly as the code comment claims
With `k2` leaked after the run, `m2` falls (it was sealed under the leaked key; not a defect) and `m0`, `m1` stay confidential. "A key recovered in epoch N does not yield epoch N-1" is now checked, not just stated.

### T3 (limit, real): no post-compromise security
With `k0` leaked after the run, every record falls. The chain is `k(n+1) = H(k(n), n+1)` with no fresh entropy, so compromise of any epoch key exposes that epoch and all later ones. The `REKEY_EVERY_RECORDS` comment in `src/relay.rs` said the ratchet bounds "how much traffic a single compromised key exposes"; that is true only backward. The comment now says so. Closing this needs fresh key material injected into the chain (an ML-KEM encapsulation every K epochs, or a re-handshake), which is a protocol change tracked as backlog **B11**. Until then the honest statement is: a leaked epoch key exposes the rest of that connection, and a connection is re-keyed from scratch only by reconnecting.

### T4 (code observation, outside the model): the previous epoch key is not zeroized
`maybe_ratchet` overwrites `self.key` and replaces the `Aes256Gcm` instance; neither the previous 32-byte key nor the previous expanded key schedule is explicitly zeroized (`zeroize` is already a dependency). Backward secrecy in practice, not just in the model, depends on the old key not lingering in memory. Small hygiene item, tracked with B11.

### T5 (holds by construction): nonce uniqueness
The counter restarts every epoch, but the nonce carries the epoch in its top four bytes and the key changes with the epoch, so no (key, nonce) pair repeats within a connection, and the per-connection handshake key keeps pairs distinct across connections. In the model this is the fact that `n0`, `n1`, `n2` are distinct and the key is per session; Verifpal 1.x would have reported a reuse otherwise.

## How to say this

Say: *"The relay record layer is symbolically verified (Verifpal 1.4.10, three epochs, 2 sessions unchanged at 3) for confidentiality and injective authentication of every record, and the one-way ratchet is verified to give backward secrecy: a key recovered later does not expose earlier epochs. It does not give post-compromise security; a compromised epoch key exposes the rest of that connection."*

Do not say: "the ratchet limits the damage of a key compromise" without the direction, "forward-secure records", or anything implying the counter-based rekey adds entropy.
