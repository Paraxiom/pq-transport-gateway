# PQTG Performance Validation Plan — 1 week, 1 Kria

**Date**: 2026-05-24
**Audience**: regional-bank (15-DC) pre-deployment performance evaluation
**Constraint**: 1 week total, 1× Xilinx Kria KR260 available
**Owner**: Sylvain Cormier, Paraxiom Technologies Inc.

---

## 1. Goal

Characterize PQTG's performance overhead when placed in front of a
QKD-controller's classical-TLS API. Produce numbers the bank can drop
straight into their architecture review:

- handshake latency (P50/P90/P99)
- per-request latency overhead after session establishment
- sustained throughput on a single Kria
- CPU and memory consumption on the gateway host
- behavior under session reuse vs. handshake-per-request

The numbers feed an SLO-compatibility line: "given the bank's
max-admin-API-latency tolerance of X ms, PQTG fits / doesn't fit."

### Out of scope

- QKD-key-mix performance (Phase 2.2 of the broader roadmap, no QKD
  device in this loop)
- Multi-host horizontal scaling (single Kria only)
- Real-vendor KMS interop (separate KirQ pilot effort)
- Production-image vendor compatibility (deliberately uses our own mock
  KMS to isolate PQTG's contribution to the latency budget)

---

## 2. Bench setup

See `docs/diagrams/performance-validation-bench.png`.

| Component | Where it runs |
|-----------|---------------|
| **PQTG Rust binary v2.0.0+** | Kria KR260 (Yocto Linux, Zynq UltraScale+, 4 GB DDR4) |
| **Mock KMS** (ETSI 014 emulator, httpmock-based — same as integration test suite) | Kria KR260, loopback to PQTG |
| **Test client** (synthetic admin-API workload generator, Rust) | Sylvain's laptop |
| **Network** | One isolated LAN segment between laptop and Kria's PS GEM (eth0) |

The mock KMS lives on the same Kria *deliberately* — it eliminates KMS
performance as a confounding variable so the measured numbers are
PQTG-attributable. This is a control-plane characterization, not a
real-vendor interop test.

---

## 3. Day-by-day schedule

| Day | Activity                                                | Output                       |
|-----|---------------------------------------------------------|------------------------------|
| 1   | Yocto flash, PQTG deploy, mock KMS boot, sanity tests    | Bench operational            |
| 2   | Handshake characterization (primitive-level + end-to-end) | Latency tables               |
| 3   | Per-request latency, throughput sweep                    | Throughput tables            |
| 4   | CPU / memory profiling, session-reuse experiment         | Resource tables              |
| 5   | 24 h continuous soak at moderate rate                    | Stability evidence           |
| 6   | Failure-mode tests (KMS down, malformed handshakes)      | Robustness evidence          |
| 7   | Report writeup                                           | 5-pp deliverable for bank    |

Each day produces a discrete artifact. If something slips, we cut the
soak from 24 h to 12 h on Day 5 to keep the schedule.

---

## 4. Measurements

### A. Handshake latency (Day 2)

**Per-primitive** — criterion benches on the Kria's ARM Cortex-A53 cores:

| Primitive                            | Target threshold (informational) |
|--------------------------------------|----------------------------------|
| ML-KEM-768 keypair generation        | < 5 ms                           |
| ML-KEM-768 encap                     | < 1 ms                           |
| ML-KEM-768 decap                     | < 1 ms                           |
| Falcon-512 sign                      | < 50 ms                          |
| Falcon-512 verify                    | < 5 ms                           |
| SLH-DSA-Shake128f sign               | < 100 ms                         |
| SLH-DSA-Shake128f verify             | < 5 ms                           |
| SHA3-256 transcript                  | < 100 µs                         |

**End-to-end PQTG handshake:**
- 10,000 sequential handshakes, P50 / P90 / P99 / P99.9 latency
- Comparison against a baseline classical-TLS handshake on same Kria
- Cold-start vs warm-start (process resident vs first connection)

### B. Per-request latency (Day 3)

Steady-state ETSI 014 admin-API calls after PQ session established:

- Single client, varying request rate: 1 / 10 / 100 / 1000 req/s
- Per-request P50 / P90 / P99
- Decomposition: PQ-decrypt → forward-to-mock-KMS → respond-to-client

### C. Throughput sweep (Day 3)

- Concurrent clients: 1 / 4 / 16 / 64
- Saturating request rate per Kria
- Latency-vs-load degradation curve (the "knee" of the curve is the
  recommended operating point)

### D. Resource consumption + session reuse (Day 4)

Profiling under steady-state load:
- CPU utilization, all 4 ARM cores, mean + peak
- RAM footprint (RSS time-series)
- Network bandwidth on PS GEM NIC

Session-reuse experiment:
- TLS-session-resumption / keep-alive vs handshake-per-request
- Effective amortization of PQ handshake cost across N requests
- Recommended session-lifetime parameter for the bank's deployment

### E. Soak (Day 5)

24 h continuous load at moderate rate (10 req/s, steady):
- Memory leak detection — RSS within ±10 % of baseline
- FD leak — `lsof` count stable
- Handshake success rate ≥ 99.9 %
- Process uptime ≥ 23.5 h

### F. Failure-mode tests (Day 6)

| Scenario                                          | Expected behavior                                              |
|---------------------------------------------------|----------------------------------------------------------------|
| Mock KMS becomes unreachable mid-session          | PQTG returns structured ETSI 014 503; reconnects when KMS returns |
| Mock KMS returns 503 (no keys)                    | 503 propagated to client cleanly                               |
| Truncated TLS connection PQTG → mock KMS          | Connection re-established; brief client-visible retry          |
| Malformed PQ handshake from client                | Reject cleanly, log, no crash, no leak                         |
| 1000 simultaneous handshake attempts              | Graceful degradation, no panic                                 |

---

## 5. Deliverable — 5-pp performance brief

Structure for the bank's architecture review:

1. **Headline numbers** — handshake latency, per-request overhead, max throughput on the Kria
2. **Resource sizing** — recommended host class per N concurrent clients
3. **Best-practice notes** — session-reuse parameters, polling cadence guidance, NIC partitioning
4. **SLO-compatibility analysis** — given bank's stated max-admin-API-latency, where does PQTG fit
5. **Caveats and follow-on** — what this test does *not* cover (real-vendor interop, multi-host scaling, QKD-key-mix overhead)

---

## 6. Inputs required from the bank before §5 item 4 can be finalized

To produce the SLO-compatibility line:

- **Max latency tolerance** on control-plane / admin APIs (P99 or P95 ms)
- **Expected concurrent control clients** per data center
- **Expected per-client request rate** (per second, range)
- **QKD vendor target** (or vendor list, if multi-vendor mode)
- **Session-lifetime preference** (security / performance tradeoff)

The §5 brief includes a placeholder paragraph that becomes concrete
once these are answered. Even without them, the numerical body of the
brief stands on its own.

---

## 7. Pre-flight (Paraxiom-side, before Day 1)

Standing-up tasks completed before the bench week begins:

- [ ] PQTG binary cross-compiled clean for ARM Cortex-A53 (Yocto target)
- [ ] Yocto image boots on the KR260 with PS GEM brought up reliably
- [ ] Criterion bench suite runs on the Kria (all 9 primitives + handshake)
- [ ] Mock-KMS process pre-staged in the Yocto image
- [ ] Workload generator built (Rust, configurable rate / concurrency)
- [ ] Test plan reviewed (this document)
- [ ] Result-capture scripts (CSV / JSON output for each measurement)

If pre-flight slips, Day 1 absorbs the slack. If Day 1 slips, the soak
on Day 5 is the first thing to compress.

---

## 8. What this plan does NOT do

Worth stating explicitly so nobody (us, the bank, future-Sylvain
re-reading this) misreads the result:

- It does **not** test against a real vendor KMS — that's the KirQ
  Phase 1 work, separate effort, different SLOs.
- It does **not** measure end-to-end QKD secret-key-rate (SKR) — PQTG
  doesn't touch the quantum data path, so SKR is unaffected by design,
  not by measurement.
- It does **not** validate multi-Kria horizontal scaling — that's a
  Phase 3 question. Single-instance numbers are the input to that
  question, not the answer.
- It does **not** include a QKD-key-mix path — `mix_keys()` stays
  compiled-in but inactive in this test, same `[DEFAULT-1]` policy as
  the KirQ Phase 1 work.
