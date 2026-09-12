# PQTG vs eprint 2025/1671 (Hövelmanns/Planken/Schaffner/Verschoor) — internal audit, 2026-08-18

**Paper:** "QKD Oracles for Authenticated Key Exchange" — https://eprint.iacr.org/2025/1671 (QCrypt 2026 talk). Models ETSI 014 as an oracle; shows Dependent-Key attacks on hybrids whose QKD key ID is unbound; proves a QKD+triple-KEM protocol that preserves ITS.

## Verdict (one line)
**PQTG is NOT vulnerable to the paper's concrete Fig-5 attack (no XOR combining, transcript-bound session keys) — but does NOT yet meet the paper's key-ID binding requirement, and our public "CatKDF standards-track" wording overclaims the current combiner. All gaps map to the already-written v3 design.**

## Passes
- No XOR anywhere. Sole combiner: `mix_keys` = SHA3-256("pqtg-key-mixing-v2" ‖ len(qkd)₍be u32₎ ‖ qkd ‖ pqc) — crypto.rs:294-304; injective encoding; identical on origin/main.
- Session key transcript-bound for the PQC half: derive_session_key = SHA3("pqtg-session-v2" ‖ secret ‖ transcript), transcript = randoms + kem_ek + falcon_vk + kem_ct (crypto.rs:254-289).
- Delivered {key_id, key} rides only inside AES-256-GCM + Falcon-512-signed frames (proxy.rs:297-323); origin/main adds one-time `into_material()` + Zeroizing.
- Prior self-diagnosis: `docs/PROTOCOL-V3-QKD-KEYID.md` (commit ef963de) already designs key_ID/key_mode/master_sae_id/qkd_key_len into ServerHello AND the signed transcript, labels → -v3, no-silent-downgrade rules.

## Fails (fix list, in order)
1. **key_ID unbound (the paper's core concern).** key_ID never enters mix_keys, transcript_hash, or derive_session_key — it is audit-logged (proxy.rs:244) and shipped as metadata (proxy.rs:313-315) only. → **Fix = implement v3**: add key_ID + key_mode + master_sae_id + qkd_key_len to transcript_hash; bump labels to pqtg-transcript-v3 / pqtg-session-v3.
2. **Hybrid mix is server-unilateral** (client never learns key_ID; ServerHello has no field — proxy.rs:52-62), so qkd_enhanced mode can't interoperate with external clients. → v3 wire fixes; interim: ship `hybrid_session=false` (commit 71db682) to origin/main so deployed behavior matches derivable behavior.
3. **Not CatKDF-shaped** — mix_keys has no context/party-info inputs, so ETSI TS 103 744 CatKDF conformance is NOT true today. ⚠️ Our one-pager + emails say the combiner "follows the standards track (TS 103 744 CatKDF / SP 800-227)". → Either implement `mix_keys(qkd_key, key_id, pqc_key, context)` with CatKDF-style OtherInfo, or soften the wording to "designed toward" in all future materials. **Until fixed, do not repeat the conformance phrasing.**
4. **qkd_client TLS verification off by default** (`danger_accept_invalid_certs(!tls_verify)`, default false — qkd_client.rs:156). Flip default / require explicit opt-out; must be resolved before BeatQuantum assessment commences.

## Paper's requirements we should note for v3 design (beyond key_ID-in-transcript)
- Their ITS-preserving construction SPLITS keys (kqkd,m‖kqkd,s), uses the QKD secret half as OTP material, and binds via nested MACs (QKD-keyed Carter-Wegman INNER, PQC-keyed outer over (t, τ1, party IDs)) — **explicitly avoiding hashing the QKD key** (hashing voids ITS). PQTG's SHA3 mix is computationally secure — fine for our "quantum-safe transport" claim, but we must never claim ITS preservation for the mixed key. If ITS-preservation ever becomes a goal, their Fig-9 construction is the template (and an implementation-collaboration hook with the authors).
- One-time key delivery (remove-on-delivery), abort-on-missing-kID, peer-pairing enforcement at retrieval, unique kIDs, party IDs in every MAC input, one-protocol-per-key (cross-protocol kID replay).

## Talking line (Toshiba call / QCrypt), honest as of today
"We audited PQTG this week against the dependent-key model in eprint 2025/1671: the concrete attack doesn't apply — we have no XOR combining and sessions are transcript-bound — and we're implementing the key-ID transcript binding their model calls for; it was already in our v3 protocol design." (Upgrade to past tense once v3 ships.)

*Full agent evidence: session 715f1d24, workflow wf_2b55e6d3-98d journal.*
