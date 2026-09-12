# PQTG measured performance — first results

*2026-09-08. Apple Silicon, `cargo bench --bench handshake`, criterion, dev machine.
**These are the first measured numbers this crate has ever produced.** Before today the benches
existed but had never been run, and the crate did not compile.*

## Results

| Operation | Primitive | Time |
|---|---|---|
| `server_identity_keygen` | Falcon-512 + SLH-DSA-Shake128f | **7.27 ms** |
| `client_kem_keygen` | ML-KEM-768 | 33.0 µs |
| `encapsulate` | ML-KEM-768 | 31.7 µs |
| `decapsulate` | ML-KEM-768 | 66.2 µs |
| `transcript_hash` (~3.2 KB) | SHA3-256 | 5.5 µs |
| `falcon_sign_transcript` | Falcon-512 | **326 µs** |
| `falcon_verify_transcript` | Falcon-512 | 30.0 µs |
| `derive_session_key` | SHA3-256 | 250 ns |
| `full_handshake_e2e` | all of the above | **7.59 ms** |

## What these say

**Connection setup is cheap enough to ignore.** The end-to-end handshake is 7.59 ms, of which
7.27 ms is identity keygen. A real server generates its identity once at startup, not per
connection, so the marginal cost of accepting a connection is roughly **0.3 ms**. That is not a
constraint for a relay.

**Per-message Falcon is the design defect, and now it is quantified.** `proxy.rs` signs and verifies
every frame with Falcon-512. At 326 µs to sign plus 30 µs to verify, that is **~356 µs of asymmetric
crypto per frame**, capping a single-threaded relay at roughly **3,000 frames per second** on
signature work alone, before any I/O.

Against `derive_session_key` at 250 ns, the per-frame asymmetric work is over **1,000× more
expensive** than the symmetric path it sits on top of. For a libp2p link carrying block announces,
transaction gossip, coherence votes and Kademlia traffic, that is the wrong shape.

**Conclusion, now evidence-backed rather than argued:** move Falcon to the handshake only and use
AEAD-only records for the data path, which is what qssh already does. This was recommended on
2026-09-07 from code reading; the measurement confirms it and puts a number on it.

⚠️ Before removing per-message Falcon, add a **client transcript signature to the handshake**. Today
the per-message signature is the only client authentication in the protocol, so deleting it first
would weaken the design rather than improve it.

## Build fixes required to get here

The crate did not compile.

The crate carried a family of release-candidate pins (`signature`, `pkcs8`, `spki`, `sha2`) under a
comment saying `ml-dsa-rc.7` would not compile against the releases. That is no longer true:
paraxiom-pqc's own CI builds `ml-dsa` against the released versions.

Keeping the rc pins meant **this tree resolved a different `pkcs8` than paraxiom-pqc resolves for
itself**, and the vendored `slh-dsa` patch is written against the release API
(`Error::KeyMalformed(KeyError)`), which does not exist in `0.11.0-rc.11` where `KeyMalformed` is a
unit variant. So the two trees could not both build.

Fix: drop the rc pins so both resolve the same versions. **No vendored crypto was modified.**

> A first attempt patched the vendored `slh-dsa` to match the rc API instead. That built locally and
> broke paraxiom-pqc CI immediately, because CI resolves the release. Reverted. The lesson worth
> keeping: when two trees disagree about a dependency version, fix the disagreement, not the code
> that is correct in one of them.

After the fix: `cargo check` clean, **48 tests pass** (39 unit + 9 integration), benches run.

## Not measured

Throughput and latency of a byte relay, because no relay exists yet. Do not quote a bytes-per-second
figure for PQTG in any document or pitch until one does.
