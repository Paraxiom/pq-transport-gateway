# A QuantumHarmony devnet whose consensus runs over PQTG

*2026-09-08. Four validators, every peer to peer edge carried by the post-quantum relay, producing
and finalizing blocks. This is Phase 0 of `docs/ops/pq-transport-activation-plan-2026-09-07.md`.*

## What was actually run

`quantumharmony/scripts/devnet-relay.sh up`

Four `quantumharmony-node` processes, four relay servers and twelve relay clients, one per ordered
pair. Each node runs `--reserved-only` with its reserved addresses pointing at its own local relay
clients, so a node has no address by which it could reach a peer directly.

```
node i  --plaintext-->  relay client (i to j)  ==ML-KEM-768 + Falcon-512 + AES-256-GCM==>  relay server j  -->  node j p2p
```

That shape is not a demo shortcut. It is what a real deployment looks like: one relay server in
front of each validator's p2p port, and one relay client per peer that validator dials.

## Result

| | |
|---|---|
| validators | 4, all authoring |
| peers per node | 3, a full mesh |
| best block | 47 |
| finalized | 45, lag 2 |
| supermajority events | 19, each logged `4/4 validators voted` |
| relay processes | 16, plus the sixteen key schedules they own |
| relay errors | none |
| connections into a validator p2p port | 12, **all of them from a relay** |
| direct validator to validator connections | **0** |

Finality advances in bursts rather than smoothly, which is the window based coherence gadget
behaving normally, not a transport artefact. All four nodes agree on the finalized head throughout.

## How the claim is checked

`devnet-relay.sh proof` does not read logs. It enumerates live TCP sockets, resolves **both** ends of
every connection touching a validator p2p port, and fails unless the process at the far end is a
relay.

That strictness was earned. An earlier, looser version of the check classified any connection from a
`quantumharmony-node` process as benign, and it waved through a stray node that had been running on
this machine since 21 August out of an abandoned job directory, listening on all interfaces and
dialling the devnet directly. It also happened to use node key `...0001`, so it shared a libp2p peer
id with devnet node 1, which is why node 1 initially showed no inbound connections at all. The
lesson generalises: a proof that trusts a process name proves nothing.

## What had to be written first

Two gaps in the relay would have made a soak meaningless.

**A peer that dies without sending a FIN.** Machine loses power, NAT drops the mapping, cable is
pulled. The spliced connection sat blocked on a read that would never return and never error. The
socket, the task and the entry in the live connection count all leaked, and libp2p was never told
the peer was gone, so it never redialled. Fixed with TCP keepalive on every socket the relay
touches: idle 30 s, probe every 10 s, three attempts, so a dead peer surfaces in about a minute.

**A peer that is alive but has stopped speaking.** Keepalive cannot see this, because the socket is
healthy. Fixed with an idle reaper at ten minutes, far longer than libp2p's own ping interval, so a
working link never trips it.

Both are covered by tests: `a_connection_where_nothing_moves_is_reaped` and
`every_relay_socket_gets_keepalive_and_no_nagle`. 98 tests pass.

## The 24 hour soak, completed 2026-09-09

The run above was under an hour. It was then left running for a full day, sampled once a minute.

| | start | after 24 h |
|---|---|---|
| blocks | 47 | **23,096** |
| finalized | 45 | 23,085 |
| supermajorities, all `4/4 validators voted` | 43 | **19,320** |
| **key ratchets, no message on the wire** | 0 | **34** |
| relay resident memory | 158 MB | **35 MB** |
| relay file descriptors | 250 | **221, flat throughout** |
| relay warnings or errors | 0 | **0** |
| connections killed by the idle reaper | 0 | **0** |

Three things in that table matter more than the block count.

**The ratchet fired 34 times on real consensus traffic with no reconnect.** Rekeying is the one thing
the previous qssh tunnel could not do: 508 attempts, 508 failures, dead since July. Here it is silent
by construction, and a day of validator traffic crossed 34 epoch boundaries without either end
noticing.

**File descriptors were flat for 24 hours** across 16 relay processes. That is the leak question
answered.

**The idle reaper never fired**, which was the risk in adding it. Ten minutes was chosen as far
longer than libp2p's own keepalive, and a full day of real traffic confirms no healthy validator
link ever goes quiet that long. It has not introduced a new source of connection churn.

## ⚠️ The relay is bypassable, and it fails OPEN (found 2026-09-09)

Fault injection killed node 4's relay server and every relay client touching it, 7 of 16 processes.
Node 4 did not lose a single peer. It reconnected **directly** to nodes 1, 2 and 3 on their real p2p
ports, in plaintext: ten unrelayed node-to-node connections where there should have been none.

Cause: `--reserved-only` restricts which **peers** a node will talk to, not which **addresses**.
libp2p identify advertises each node's real listen address, peers learn it, and when the tunnel dies
they redial the peer directly.

**In production this is a silent security failure.** A relay crashes on a validator and, instead of
losing connectivity, the validator quietly speaks plaintext to its peers. Nothing alerts, finality
keeps advancing, and the post-quantum property is simply gone until someone runs a socket audit.

This does not affect the 24 hour soak above: all 16 relays were alive throughout and `proof` passed
twice, every connection crossed a tunnel. What is new is the behaviour when one dies.

**The fix is a deployment property, not a code change.** Bind each node's p2p listener to `127.0.0.1`
only and make the relay server the sole externally reachable endpoint. A dead relay then means no
connectivity: visible, loud, fail-closed. Optionally also set `--public-addr` to the relay address so
the real port is never advertised at all.

**No validator cutover should happen until that binding is written into the procedure.**

## What this does not show

- **One machine.** Loopback between the relays. The WAN cost is measured separately in
  `BENCHMARKS-WAN-2026-09-08.md`: 0.3 ms at the median on an established connection, 97 percent of
  link throughput.
- **Under an hour.** Not a 24 hour soak. Long enough to see 19 supermajorities and no relay error,
  not long enough to see a ratchet boundary at 65,536 records or a memory trend.
- **No faults injected.** No node killed, no partition, no relay restarted mid flight. Reconnect
  behaviour is therefore argued from design and from the reaper tests, not demonstrated here.
- **Not production.** Nothing in this run touched Alice, Bob or Charlie. Per the activation plan
  nothing goes near a production validator before the coherence gadget fix has soaked, which is not
  before 2026-10-16.

## Next

1. A 24 hour soak of this same devnet, watching for ratchet boundaries and memory growth.
2. Fault injection: kill a relay mid flight and confirm libp2p redials through a fresh tunnel.
3. Only then, a canary on a zero quorum node.
