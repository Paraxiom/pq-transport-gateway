# PQTG relay over a real network — first WAN measurement

*2026-09-08, late afternoon. Not loopback, not a lab. A residential link in the Laurentians to an
OVH VPS in Beauharnois, over the public internet, ~16 ms round trip. The VPS is a disposable host
and is **not** a validator.*

## Topology

```
laptop                                    OVH VPS, Beauharnois
------                                    -----------------------
bench ──► 127.0.0.1:9444                  0.0.0.0:9443 relay server
          relay client  ══ internet ══►   │
          (plaintext in,                  └──► 127.0.0.1:9500 echo backend
           ML-KEM + Falcon out)
```

The baseline uses the same bench binary pointed straight at a plain TCP echo on the VPS, so the
comparison isolates PQTG from the link.

## Results

| | plain TCP | PQTG relay | cost of PQTG |
|---|---|---|---|
| **steady state p50** | 13.7 ms | **14.0 ms** | **+0.3 ms** |
| **steady state p95** | 16.8 ms | **17.6 ms** | +0.8 ms |
| throughput, 8 MiB echo | 3.7 MiB/s | **3.6 MiB/s** | 97% of the link |
| connection setup p50 | 15.4 ms | 51.1 ms | +36 ms, once per connection |
| payload integrity | ok | ok | |

Steady state is 200 round trips of 64 bytes on one already established connection, which is how a
validator uses a peer link. Connection setup is measured separately because it happens once.

## Reading these

**The data path is effectively free.** Once a connection is up, ML-KEM key agreement, Falcon
authentication, AES-256-GCM records and a SHA3-256 ratchet cost 0.3 ms at the median against a
13.7 ms link. That is under 3 percent, and it is inside the run to run variance of the link itself.
Consensus votes are small and frequent, and this is the number that decides whether they can be
carried. They can.

**Throughput is the link, not the relay.** 3.6 against 3.7 MiB/s is 97 percent. The absolute figure
is a residential uplink, not a PQTG ceiling. The earlier loopback figure of 40.6 MiB/s is the
relevant upper bound for a datacentre path.

**Setup costs two extra round trips.** 51 ms against 15 ms is one TCP connect to the relay server
plus one handshake round trip, on top of the link. Nothing here is compute: the whole cryptographic
handshake measures 7.59 ms on this machine and 0.3 ms marginal once the identity exists
(`BENCHMARKS-2026-09-08.md`). The 36 ms is network latency, and it is paid once per connection, not
per message. Long lived validator peerings pay it at startup and never again.

## One real bug this found

The first WAN run measured **p50 137.3 ms against a 16.4 ms link**. Eight times the round trip is
not a cryptographic cost, and no amount of profiling the cipher would have found it.

`write_len_prefixed` writes a length and then a body as two separate writes. Nagle's algorithm held
the second write waiting for an acknowledgement of the first, and the peer's delayed acknowledgement
timer held that acknowledgement for up to 40 ms. The two interact badly and the pattern is well
known. `TcpStream::set_nodelay(true)` at the four points where a socket enters the relay removed it:

| | before | after |
|---|---|---|
| setup p50 | 137.3 ms | 50.6 ms |
| steady state p50 | not measured | 14.0 ms |

This is the argument for measuring over a real link rather than loopback. On loopback there is no
delayed acknowledgement timer and the defect is invisible.

## What this does not show

- One client, one server, one connection at a time. No mesh, no four node soak.
- No packet loss, no reordering, no path change. A single clean 16 ms path.
- No reconnect and no dead peer detection. The relay has a ratchet and no rekey message on the
  wire, so it does not have the failure that killed the qssh tunnel, but that is an argument from
  design and not yet from a soak.
- The VPS is not a validator and no consensus traffic crossed this link.

## Reproducing

```
# on the remote host
relay_wan echo   127.0.0.1:9500
relay_wan server 0.0.0.0:9443 127.0.0.1:9500
relay_wan echo   0.0.0.0:9444            # baseline, plain TCP

# on the near host
relay_wan client 127.0.0.1:9444 <remote>:9443 --pin SHA3-256:<fingerprint the server printed at startup>
# (since 2026-09-12 the client refuses to start without --pin; --insecure-no-pin only for a bench on a trusted link)
relay_wan bench  <remote>:9444 8         # baseline
relay_wan bench  127.0.0.1:9444 8        # through the relay
```
