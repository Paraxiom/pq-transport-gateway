# PQTG gateway session layer: results (2026-10-15)

*This covers `PqSession` in `src/crypto.rs` on branch `fix/gateway-session-direction-keys`, where the fix is commit 70be762 (wire `3.2` and `2.1`). The design: one AES-256-GCM key per direction, `k_c2s` and `k_s2c` derived from the session key by HMAC-SHA3-256 under distinct domains; each direction counts nonces from 0; strict receive sequencing. The handshake is out of scope here and has its own models and results in this directory.*

**What this document is.** A record of what was run on 2026-10-14 and 2026-10-15 and what each run shows. Nothing here is an audit, and nothing here proves the gateway secure.
- The Verifpal results are symbolic and bounded.
- The property tests, the fuzzing and the mutation testing are tests.
- Of the seven Kani harnesses, one ran to a verdict. It covers one small function.

Each section says what its tool assumes.

## Summary

| Check | Result |
|---|---|
| Verifpal, fixed record layer (with and without the inner Falcon signature) | every confidentiality and authentication query holds at 1, 2 and 3 sessions |
| Verifpal, the pre-fix design (one key for both directions) | nonce reuse found by the tool; all four plaintexts and both responses' authenticity lost |
| Verifpal, one direction key leaked | that direction lost, the other direction holds |
| Verifpal + Rust test, `k_c2s` leaked, signed frames | **limit:** a request the client really signed can be replayed at a later position or into another session (the inner signature binds no session, direction or position) |
| Property tests (`tests/session_model.rs`) | 65,536 cases per variant, 0 failures; no (key, nonce) pair repeated; every replay, reorder, reflection, bit flip, truncation and forgery refused with no state change |
| Fuzzing, 4 targets, 240 s each | 5,162,082 executions in total, 0 crashes, 0 artifacts |
| cargo-mutants on the session code | 37 distinct mutants: 29 caught, 2 unviable, 6 missed. 3 of the missed were real gaps and are now caught by new tests; the other 3 are equivalent |
| Kani (bounded model checking, cipher replaced by a model) | 1 of 7 harnesses verified (`session_nonce` injective); 2 hit a Kani limitation; 4 gave no verdict within 25 minutes |
| Full test suite | all tests pass except one pre-existing relay timing test that fails intermittently under heavy machine load (details in the last section) |

## 1. Verifpal models

Tool: Verifpal 1.4.10 (`~/.local/bin/verifpal`), active attacker.

**Code mapping.** Each model has two requests and two responses over one session, in the order `handle_session` runs them.
- **Session key.** `session_key = HASH(lbl_session, ss)` from an ephemeral KEM whose public key and ciphertext are delivered guarded. This stands in for the signed, pinned, allow-listed handshake, as in `pqtg-relay-ratchet.vp`.
- **Direction keys.** `k_c2s = MAC(session_key, lbl_c2s)` and `k_s2c = MAC(session_key, lbl_s2c)` (`kdf::prf`).
- **Frames.** Frame n is `AEAD_ENC(k_dir, n_n, m, nil)`. Both directions use the same public nonce constants `n0` and `n1`, because each direction counts from 0 and only the keys differ.
- **Receiving.** `AEAD_DEC(...)?` at the slot's own nonce. This is the strict receive rule, as far as fixed slots can express it.

**This Verifpal reasons about AEAD nonce reuse.** It reports an attack when two ciphertexts share a key and a nonce, which is what makes the regression model meaningful.

**Result codes.** One letter and digit per query, in this order: `req0 req1 resp0 resp1` (confidentiality), then `q0 q1 a0 a1` (authentication of each frame). `0` means the query holds; `1` means an attack was found. Every model gave the same code at `--sessions 1`, at the default of 2 sessions, and under `--saturate` (unchanged from 2 to 3 sessions). The models were written and first run on 2026-10-14. On 2026-10-15 all of them were run again and gave identical verdicts. The leak-s2c and signed-leak-c2s models are new on 2026-10-15. Saved outputs: `verifpal-output-gateway-session*.txt`, with the suffixes `-1session` and `-saturate`.

| Model | Code | Reading |
|---|---|---|
| `pqtg-gateway-session.vp`: the fixed record layer | `c0c0c0c0a0a0a0a0` | **Holds.** No request or response leaks. No frame is accepted unless its legitimate sender sent it in that slot: no substitution, and no replay into another slot (`n0` and `n1` differ). It also covers **reflection to the client**: the active attacker may put the observed `q0` into `a0`'s slot, and the client refuses it because `k_c2s` is not `k_s2c`. |
| `pqtg-gateway-session-signed.vp`: the same plus the inner Falcon-512 signature of `sign_and_encrypt` | `c0c0c0c0a0a0a0a0` | **Holds**, as above. |
| `pqtg-gateway-session-onekey.vp`: regression with one key for both directions (wire 2.0 / 3.1), strict receive kept | `c1c1c1c1a0a0a1a1` | **The fixed bug, found by the tool.** Every confidentiality trace reads "a0 shares its key and nonce" with q0 (and the same for each pair): this is cross-direction nonce reuse. The responses also lose authenticity, because the attacker forges under the shared (key, nonce). |
| `pqtg-gateway-session-onekey-signed.vp`: regression plus the inner signature | `c1c1c1c1a0a0a1a1` | **The inner signature did not save the old design.** Confidentiality falls as above. For `a0`, the attacker recovers a server-signed response from a parallel session and splices it into this one, and the signature verifies, because it binds no session. |
| `pqtg-gateway-session-leak-c2s.vp`: fixed design, `k_c2s` leaked before any frame | `c1c1c0c0a1a1a0a0` | **What holds under a key leak.** Requests lose confidentiality and authenticity. Responses keep both, because `k_s2c` is a separate PRF output and cannot be derived from `k_c2s`. |
| `pqtg-gateway-session-leak-s2c.vp`: fixed design, `k_s2c` leaked | `c0c0c1c1a0a0a1a1` | The mirror image: responses are lost and requests hold. |
| `pqtg-gateway-session-signed-leak-c2s.vp`: signed frames, `k_c2s` leaked | `c1c1c0c0a1a1a0a0` | **Limit L6** (see §2). The traces for `q0` and `q1` use content the client really signed. For `q0`, it is a signed request from session #2 re-sealed under this session's leaked key. For `q1`, it is this session's signed request 0 re-sealed at position 1. The server's signature check passes both times. |

**How to read the regression models.**
- **Confidentiality.** In the symbolic model, nonce reuse gives the attacker the whole plaintext. Real AES-GCM nonce reuse gives the XOR of the two plaintexts, which recovers both only when one of them is known or guessable. A gateway request is a short JSON `KeyRequest`, so that condition is plausible, but the symbolic verdict over-approximates.
- **Authentication.** The failures match the real attack. Two GCM messages under one key and nonce let an attacker solve for the GHASH key, Joux's "forbidden attack", and then forge under that nonce.
- **What the regression keeps.** It keeps the strict receive rule of the fixed code. The pre-fix code also accepted a frame at any nonce, so it was weaker than this model, not stronger.
- **Why `q0` and `q1` hold.** In `onekey`, `q0` and `q1` authentication hold only because of ordering: the matching response does not exist yet when each request is opened.

**What the models do not cover.**
- **Reflection to the server, at the counter the server expects.** Because of the lockstep order, the server never holds its own frame for a slot before it has to receive that slot, so fixed slots cannot express this case. The evidence for it is the property tests (§3: `refused_reflected_at_matching_counter`) and the unit test `a_frame_reflected_to_its_sender_is_rejected` from 70be762. Verifpal is not credited with it.
- **The rest.** Counter exhaustion; more than two frames per direction; real AES-GCM (the AEAD is ideal); real HMAC-SHA3-256 (MAC is an ideal one-way keyed function); the handshake (stood in for); traffic analysis.
- **Bounds.** Verifpal is bounded and incomplete. "Holds" means no attack was found within 3 sessions.

## 2. Limit found: the inner signature binds no session or position (THREAT-MODEL L6)

`sign_and_encrypt` signs the data only. While both direction keys are secret, this costs nothing, because the AEAD already binds each frame to its session, direction and position. If `k_c2s` leaks, an attacker can open a captured signed request and re-seal it:
- at a later position of the same session, or
- into another session whose `k_c2s` it also holds.

The gateway accepts it in both cases. The attacker still cannot produce a request the client never signed, and cannot read or forge responses.

`tests/session_key_leak.rs` shows this on the real code, for both v2 and v3:

| Test | Shows |
|---|---|
| `limit_leaked_c2s_lets_a_signed_request_be_replayed_at_a_later_position` | the replay is accepted, and the genuine request 1 is then refused |
| `limit_leaked_c2s_lets_a_signed_request_cross_into_another_session` | the cross-session splice is accepted |
| `holds_leaked_c2s_does_not_let_the_attacker_make_unsigned_requests` | refused: garbage signature, the client's signature over other data, the server's signature, empty signature |
| `holds_leaked_c2s_does_not_expose_or_forge_responses` | `k_c2s` does not open a response; a frame sealed under `k_c2s`, or the request reflected, is refused by the client |

The two `limit_*` tests pass because the limit exists. If the signature is later bound to session id, direction and counter, they must fail and be turned around. That would be a wire change, and it is **not** made on this branch.

## 3. Property tests: `tests/session_model.rs` (proptest, pure Rust, dev-dependency)

Each case draws a session key, a version and up to 48 operations (24 in the full-frame variant):
- honest sends, deliveries, losses and swaps in flight;
- replay of any earlier frame;
- reflection to the frame's own sender;
- one-bit flips, truncation;
- forgery at the expected counter under another session's key, the other version's key, or the opposite direction's key.

After every operation, the real ends are compared with a reference model:
- **Acceptance.** A frame is accepted if and only if it is an unmodified frame of the receiver's direction at the receiver's counter. When accepted, it yields exactly what was sealed and moves that one counter by one.
- **Refusal.** Anything else is refused, and no counter moves.
- **Sealing.** Every sealed frame carries `session_nonce(n)` for the sender's own counter, and opens under its own direction key and not the other, checked by trial decryption with an independent `aes-gcm` instance.
- **No reuse.** No (key, nonce) pair occurs twice in the session across both directions.
- **Recovery.** At the end, all withheld frames are delivered in order and open, then one more frame each way.

There is also a scripted test, `the_model_accepts_honest_traffic_and_refuses_each_attack`, which checks that the model is not vacuous.

| Run | Variant | Cases | Ops | Frames sealed and accepted | Refused: out of place / reflected (at matching counter) / flipped / truncated / forged |
|---|---|---|---|---|---|
| default (`cargo test`) | record layer | 256 | 5,995 | 1,834 | 479 / 434 (180) / 446 / 238 / 378 |
| default | full frames (real Falcon-512) | 16 | 214 | 87 | 10 / 15 (11) / 10 / 8 / 13 |
| `PROPTEST_CASES=4096 --release` | record layer | 4,096 | 95,882 | 29,396 | 7,559 / 7,308 (2,990) / 7,294 / 3,688 / 5,264 |
| | full frames | 4,096 | 46,471 | 18,464 | 2,019 / 2,555 (1,495) / 2,588 / 1,316 / 2,540 |
| `PROPTEST_CASES=65536 --release` | record layer | 65,536 | 1,537,901 | 473,193 | 122,417 / 117,589 (46,936) / 117,285 / 58,598 / 85,597 |
| | full frames | 65,536 | 753,774 | 299,102 | 32,714 / 41,352 (24,115) / 41,308 / 20,436 / 41,717 |

All runs had 0 failures. "Frames sealed" includes the two frames per case that the final drain step sends. Counters are read from the public `Debug` output, which prints counters and no key material.

## 4. Fuzzing: `fuzz/` (cargo-fuzz, libFuzzer)

**Setup.**
- **Toolchain.** `cargo +nightly fuzz run -O <target> fuzz/corpus/<target> fuzz/seeds/<target> -- -max_total_time=240 -print_final_stats=1`, with `-max_len` and `-malloc_limit_mb` as given in each target's header.
- **Starting corpus.** The corpus from the interrupted 2026-10-14 runs, plus the committed seeds.
- **Library version.** Before the runs, `fuzz/Cargo.lock` (not committed, it is gitignored) was pinned by hand to the gateway's own `paraxiom-pqc` rev, c0ee1f7 (0.1.3). Left alone, it had resolved 0.1.4, because `Cargo.toml` named the git repository with no rev. Since the follow-up commit, `Cargo.toml` and `kani/Cargo.toml` pin `rev = "c0ee1f7…"`, and `fuzz/` inherits it through the path dependency: a fuzz build from a fresh lock (old lock moved aside) resolved paraxiom-pqc 0.1.3 at c0ee1f7.
- **Concurrency.** Kani was running on other cores at the same time, so execution rates are lower bounds.

Each target asserts properties, not just "no panic". The full list is in each file's header.

| Target | Input reaches | Asserted | Executions | exec/s | New units | Crashes |
|---|---|---|---|---|---|---|
| `session_frame` | `decrypt_and_verify` on arbitrary frames at receive counter 0 to 3, either role, v2/v3 | never Ok; a refused frame moves no counter; the genuine next frame still opens | 2,131,896 | 8,846 | 2 | 0 |
| `session_payload` | the length prefix, split and Falcon verify of an authenticated payload (raw or patched valid template) | no panic; counter moves exactly once; Ok only for a payload whose signature verifies under the client key | 1,146,294 | 4,756 | 566 | 0 |
| `gateway_messages` | bincode decode of the version peek, `ClientHello`, `ClientHelloV3` (+ `digest`), `KeyRequest` | no panic, no allocation above 64 MB | 1,843,976 | 7,651 | 109 | 0 |
| `server_hello_path` | a real `ProxyServer` over loopback TCP: frame reader, version match, decode, allow-list, v3 signature/freshness/replay, encapsulation, session loop | no panic; every connection finishes within 60 s of the peer closing; no allocation above 64 MB | 39,916 | 165 | 188 | 0 |

The exit code was 0 for all four, and `fuzz/artifacts/*` was empty afterwards.

`session_frame` coverage stayed flat (415 edges). That is expected: without the key, nothing gets past the AEAD, so the fuzzer can only exercise the refusal paths. The interesting parsing is in `session_payload`, which starts after authentication.

**Zero-C.** `libfuzzer-sys` builds libFuzzer (C++) through `cc`. This is confined to the standalone `fuzz/` workspace, which is not a member of the gateway's build; it was already the case before this work.

## 5. Mutation testing: cargo-mutants 27.1.0

**Run.** `cargo mutants --file src/crypto.rs --re 'PqSession|session_nonce|derive_direction_keys' -j 2 -- --lib --test session_model --test gateway_session --test session_key_leak --test kdf_kat --test handshake_kat -- --skip a_stale_or_future_dated_hello_is_refused`.
- The skipped relay test is a known flaky test (a timing margin under load), and it does not touch this code.
- cargo-mutants lists each mutant twice, because `src/crypto.rs` is compiled into both the library and the binary. The counts below are distinct mutants.

**Result.** 37 distinct mutants: 29 caught, 2 unviable (`Default` for types without it), 6 missed. All 6 were in the payload checks of `decrypt_and_verify`:

| Mutant | Assessment |
|---|---|
| line 677: `payload.len() < 4` to `== 4` | **Real gap.** A 0 to 3 byte authenticated payload would panic on the slice. Now caught by `tests/session_payload.rs` |
| line 682: `payload.len() < 4 + data_len` to `==` | **Real gap.** A prefix announcing more data than present would panic. Now caught |
| line 682: `4 + data_len` to `4 * data_len` | **Real gap.** It panics on a 1-byte announcement with no data, and wrongly refuses signed data longer than about a third of the signature (more than about 220 bytes). No test sent large signed data. Now caught |
| line 670: `encrypted.len() < 12` to `<=` | **Equivalent.** A 12-byte frame has an empty ciphertext, which `decrypt` refuses anyway with no state change; only the error text differs |
| line 677: `< 4` to `<= 4` | **Equivalent.** A 4-byte payload has no signature bytes and fails verification anyway |
| line 682: `< 4 + data_len` to `<=` | **Equivalent.** Same reason: there are no signature bytes |

A second run on `decrypt_and_verify`, with `--test session_payload` added: 19 distinct mutants, 16 caught, 3 missed, and the 3 missed are exactly the equivalent ones above.

**Not mutated.** `PqSession::new` produced no mutants (cargo-mutants does not swap match arms). The role mapping is covered instead by the opposite-direction checks in the property tests and by `gateway_session.rs`.

## 6. Kani harnesses: `kani/` (experimental, mostly no verdict)

**What the harnesses are.**
- **Code under check.** `src/crypto.rs` and `src/kdf.rs` are compiled verbatim (`kani/build.rs` reads `src/crypto.rs` at build time and inserts its text unchanged into a wrapping module; an earlier version of this line said build.rs asserts the copy is byte-identical, but that assertion was always true and has been removed).
- **Cipher.** AES-256-GCM is replaced by an oracle model (`kani/aead-model/`). It records the key and nonce of each call and lets the harness choose success or failure, and nothing is encrypted.
- **PRF.** In the role-mapping harness, HMAC-SHA3-256 is replaced by a key-XOR-domain stub.
- **Falcon.** In the full-frame harness, Falcon verification is replaced by an arbitrary outcome.
- **Errors.** `Backtrace::capture` and `anyhow`'s formatter are stubbed out.

These are bounded checks of the session logic under those replacements. They are not proofs about AES-GCM, HMAC or Falcon.

**Run.** Kani 0.67.0 on macOS arm64, `cargo kani -Z stubbing -Z unstable-options --harness-timeout 25m -j 4 --output-format=terse`. The harnesses that failed were then run one at a time.

| Harness | Result |
|---|---|
| `a_session_nonce_is_injective` | **VERIFICATION SUCCESSFUL** (61 checks, 0.3 s). For all u64 `a` and `b`: `session_nonce(a) == session_nonce(b)` iff `a == b`, and the layout is four zero bytes followed by the big-endian counter |
| `d_direction_domains_are_distinct` | FAILED on a Kani limitation, not on an assertion. The domain constants are `LazyLock` statics, and on macOS `std`'s `Once` uses `ptr_mask`, which Kani does not support (the "unsupported construct" check fails and every other check is undetermined). The same fact is a concrete unit test (`kdf::tests::every_listed_domain_is_distinct_and_stable`) |
| `d_roles_map_the_direction_keys` | FAILED, for the same `ptr_mask` reason (`derive_direction_keys` dereferences the statics) |
| `b_one_seal_from_any_state` | no verdict: CBMC timed out at 25 min |
| `b_no_nonce_repeats_in_a_run_of_seals` | no verdict: timed out at 25 min |
| `c_open_accepts_only_the_expected_nonce_and_moves_only_on_success` | no verdict: timed out at 25 min |
| `c_open_and_verify_never_panics_and_moves_only_on_an_authenticated_frame` | no verdict: timed out at 25 min in the parallel run; a solo run was stopped after 20 min |

So the one thing Kani establishes here is the injectivity of `session_nonce`. It is the base fact behind "no nonce repeats within a direction", together with a counter that only moves up by one and never wraps. That counter behaviour is tested (unit tests, property tests), not proved.

Two things would let the other harnesses run:
- running them on Linux, or replacing the `LazyLock` dereference in the harnesses, for the `d_*` pair;
- splitting the `b_*` and `c_*` harnesses or narrowing their symbolic inputs, for the timeouts.

Neither was done. The previous session's bisection probes were removed.

## 7. Full test suite

Final run (`cargo test --no-fail-fast`, debug, 2026-10-15), with `cargo fmt --all -- --check` clean. The compiler for each run is named below.

`cargo clippy --all-targets -- -D warnings` depends on the clippy version:
- clippy 1.88.0 (the local `stable` alias): exit 101, 9 `uninlined_format_args` lints, all in code this branch did not change (`src/audit.rs`, `auth.rs`, `crypto.rs` persistence code, `proxy.rs`, `qkd_client.rs`; from commit e3bf2427). That lint was in clippy's default set on 1.88.
- clippy 1.90 nightly and clippy 1.96.0: exit 0.

An earlier version of this paragraph said the lints were new in clippy 1.96 and that clippy failed there; that was backwards. Note that on this machine Homebrew's `cargo-clippy` (1.96) comes before the rustup proxies on `PATH`, so `cargo +stable clippy` silently runs clippy 1.96 unless `~/.cargo/bin` is first; the 1.88 result above was taken with `~/.cargo/bin` first.

**Doc-tests.** The two `compile_fail` doc-tests (`EphemeralKemKey::decapsulate` reuse, `ServerHandshake::into_session` reuse) imported `pq_transport_gateway::…`, but the library is named `pq_qkd_proxy`, so they failed on the bad import rather than on the move they illustrate. The `ServerHandshake` one also built its hello with `unimplemented!()`, after which the compiler does not borrow-check the rest, so it would not have failed even with the right import. Both are fixed: they import `pq_qkd_proxy`, and the handshake one takes the hello as a function argument. Checked by compiling each body as a standalone example: each fails with exactly one error, E0382, and compiles cleanly with the line that reuses the moved value removed. The blocks are tagged `compile_fail,E0382`. Rustdoc enforces that tag on nightly only: on nightly 1.90, the fixed doc-tests pass, and the same blocks with the old `pq_transport_gateway` import fail with "Some expected error codes were not found: [\"E0382\"]". On stable 1.96 the tag is ignored and a block that fails for any reason passes.

| Target | Passed |
|---|---|
| lib unit tests (`src/lib.rs`) | 131 |
| bin unit tests (`src/main.rs`, same modules) | 131 |
| `tests/etsi014_emulator.rs` | 9 |
| `tests/gateway_session.rs` | 7 |
| `tests/handshake_kat.rs` | 7 |
| `tests/kdf_kat.rs` | 4 |
| `tests/session_key_leak.rs` (new) | 4 |
| `tests/session_model.rs` (new) | 3 |
| `tests/session_payload.rs` (new) | 4 |
| doc-tests | 2 |
| **Total** | **302, 0 failed, 0 ignored** |

The relay test known to flake under load (`a_stale_or_future_dated_hello_is_refused`) passed in this run.

**Rerun after the review fixes (2026-10-15).** On this machine Homebrew's `rustc` 1.96 also comes before the rustup proxies on `PATH`, so the toolchain of each run was read from the test binaries (`/rustc/<commit>` strings). The first run was built by rustc 1.96.0 (Homebrew) and passed 302 of 302 (exit 0). The next runs were built by nightly 1.90 with `~/.cargo/bin` first on `PATH`. With the machine at a load average of 63 to 71 from other jobs, two of them each failed one test, that same relay test, in the binary's copy of the unit tests (301 passed, 1 failed, exit 101). It checks that a hello dated 121 s ahead is refused against a 120 s skew limit; when more than a second passes between building the hello and checking it, the hello falls inside the limit and is accepted, so the test fails. Run alone it passed 3 of 3. A fourth full run on nightly 1.90, at a load average near 40, passed 302 of 302 (exit 0). `src/relay.rs` is not changed on this branch (`git diff e50204d..HEAD -- src/relay.rs` is empty). The test needs a wider margin; that is a separate change.
