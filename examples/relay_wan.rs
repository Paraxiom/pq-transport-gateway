//! Post-quantum relay over a real network.
//!
//! Two roles, run on two machines, so the relay is measured across the actual
//! internet rather than loopback.
//!
//! On the remote host (the one with a public address):
//! ```text
//! relay_wan server 0.0.0.0:9443 127.0.0.1:9500     # relay listens, forwards to a backend
//! relay_wan echo   127.0.0.1:9500                  # a backend to forward to
//! ```
//!
//! On the near host:
//! ```text
//! relay_wan client 127.0.0.1:9444 <remote-ip>:9443 --pin SHA3-256:<b64>
//!                                                  # local plaintext in, PQ out,
//!                                                  # server identity pinned
//! relay_wan bench  127.0.0.1:9444 8                # push 8 MiB through and time it
//! ```
//!
//! The server prints its fingerprint at startup; `relay_wan fingerprint
//! <keyfile>` prints it for a saved (or freshly generated) identity so a script
//! can know the pin before the server is even running. A client with no pin is
//! refused unless `--insecure-no-pin` is given, and then it warns on every
//! handshake: without the pin it cannot tell the real server from an on-path
//! impostor.
//!
//! `bench` also prints per-request latency, which on loopback is meaningless
//! and over a real link is the number that decides whether this can carry
//! consensus votes.

use anyhow::{anyhow, Result};
use std::sync::Arc;
use std::time::Instant;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

use pq_qkd_proxy::crypto::PqKeyExchange;
use pq_qkd_proxy::relay::{ClientPolicy, PinPolicy, RelayClient, RelayServer, ServerPin};

#[tokio::main]
async fn main() -> Result<()> {
    // Without this the relay's own tracing goes nowhere, which is how a soak
    // ends up with empty relay logs and nothing to show for itself.
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()),
        )
        .with_target(false)
        .init();

    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage:");
        eprintln!(
            "  relay_wan server      <listen> <backend> --client SHA3-256:<b64> [--client ...] | --any-client"
        );
        eprintln!(
            "  relay_wan client      <listen> <remote> --pin SHA3-256:<b64> | --insecure-no-pin"
        );
        eprintln!("  relay_wan fingerprint <keyfile>            (creates the identity if missing)");
        eprintln!("  relay_wan echo        <listen>");
        eprintln!("  relay_wan bench       <target> <mib>");
        return Err(anyhow!("missing arguments"));
    }

    match args[1].as_str() {
        "server" => {
            let listen: std::net::SocketAddr = args[2].parse()?;
            let backend: std::net::SocketAddr = args[3].parse()?;
            let clients = client_policy_from_args(&args[4..])?;
            let identity = Arc::new(load_or_make_identity("relay_wan_server.key")?);
            let listener = TcpListener::bind(listen).await?;
            println!("relay server on {listen}, forwarding to {backend}");
            println!(
                "identity fingerprint {} (clients pin this)",
                ServerPin::of(&identity)
            );
            match &clients {
                ClientPolicy::Authorized(list) => {
                    println!("accepting {} allow-listed client(s)", list.len())
                }
                ClientPolicy::AnyClient => println!(
                    "accepting ANY client (--any-client): {backend} is reachable by anyone who can reach {listen}"
                ),
            }
            RelayServer::new(identity, backend, 256, clients)
                .serve(listener)
                .await?;
        }
        "client" => {
            let listen: std::net::SocketAddr = args[2].parse()?;
            let remote: std::net::SocketAddr = args[3].parse()?;
            let policy = pin_policy_from_args(&args[4..])?;
            let identity = Arc::new(load_or_make_identity("relay_wan_client.key")?);
            let listener = TcpListener::bind(listen).await?;
            match policy {
                PinPolicy::Require(pin) => {
                    println!("relay client on {listen}, tunnelling to {remote}, server pinned to {pin}")
                }
                PinPolicy::Unpinned => println!(
                    "relay client on {listen}, tunnelling to {remote}, UNPINNED (cannot authenticate the server)"
                ),
            }
            RelayClient::new(identity, remote, policy)
                .serve(listener)
                .await?;
        }
        "fingerprint" => {
            let identity = load_or_make_identity(&args[2])?;
            println!("{}", ServerPin::of(&identity));
        }
        "echo" => {
            let listen: std::net::SocketAddr = args[2].parse()?;
            let listener = TcpListener::bind(listen).await?;
            println!("echo backend on {listen}");
            loop {
                let (mut s, _) = listener.accept().await?;
                tokio::spawn(async move {
                    let mut buf = vec![0u8; 65536];
                    loop {
                        match s.read(&mut buf).await {
                            Ok(0) | Err(_) => break,
                            Ok(n) => {
                                if s.write_all(&buf[..n]).await.is_err() {
                                    break;
                                }
                            }
                        }
                    }
                });
            }
        }
        "bench" => {
            let target: std::net::SocketAddr = args[2].parse()?;
            let mib: usize = args.get(3).map(|s| s.parse()).transpose()?.unwrap_or(8);
            bench(target, mib).await?;
        }
        other => return Err(anyhow!("unknown role {other}")),
    }
    Ok(())
}

/// `--pin <fingerprint>` or `--insecure-no-pin`. No flag is an error: the
/// client has to say what it trusts, there is no quiet default.
fn pin_policy_from_args(rest: &[String]) -> Result<PinPolicy> {
    let mut it = rest.iter();
    let mut policy = None;
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--pin" => {
                let value = it
                    .next()
                    .ok_or_else(|| anyhow!("--pin needs a value like SHA3-256:<base64>"))?;
                policy = Some(PinPolicy::Require(ServerPin::parse(value)?));
            }
            "--insecure-no-pin" => policy = Some(PinPolicy::Unpinned),
            other => return Err(anyhow!("unknown client flag {other}")),
        }
    }
    policy.ok_or_else(|| {
        anyhow!(
            "relay_wan client needs --pin SHA3-256:<base64> (the server prints it at startup, \
             or run `relay_wan fingerprint <keyfile>`); --insecure-no-pin only for a bench on a \
             link you already trust"
        )
    })
}

/// `--client <fingerprint>` (repeatable) or `--any-client`. No flag is an
/// error: an open relay exposes its backend to anyone who can reach the port.
fn client_policy_from_args(rest: &[String]) -> Result<ClientPolicy> {
    let mut it = rest.iter();
    let mut allowed = Vec::new();
    let mut any = false;
    while let Some(flag) = it.next() {
        match flag.as_str() {
            "--client" => {
                let value = it
                    .next()
                    .ok_or_else(|| anyhow!("--client needs a value like SHA3-256:<base64>"))?;
                allowed.push(ServerPin::parse(value)?);
            }
            "--any-client" => any = true,
            other => return Err(anyhow!("unknown server flag {other}")),
        }
    }
    if !allowed.is_empty() {
        return Ok(ClientPolicy::Authorized(allowed));
    }
    if any {
        return Ok(ClientPolicy::AnyClient);
    }
    Err(anyhow!(
        "relay_wan server needs --client SHA3-256:<base64> for each allowed client (run \
         `relay_wan fingerprint <keyfile>` on the client), or --any-client only when the backend \
         authenticates its own peers"
    ))
}

fn load_or_make_identity(path: &str) -> Result<PqKeyExchange> {
    match PqKeyExchange::load_if_present(path)? {
        Some(id) => Ok(id),
        None => {
            let id = PqKeyExchange::new()?;
            id.save(path)?;
            println!("generated a fresh identity at {path}");
            Ok(id)
        }
    }
}

async fn bench(target: std::net::SocketAddr, mib: usize) -> Result<()> {
    println!();
    println!("  PQTG relay over a real network");
    println!("  ==============================");
    println!();

    // Latency: many small round trips. This is the number that matters for
    // consensus votes, which are small and frequent.
    println!("  latency, 64-byte round trips through the relay");
    let mut samples = Vec::new();
    for _ in 0..20 {
        let mut c = TcpStream::connect(target).await?;
        let msg = [0x5au8; 64];
        let t = Instant::now();
        c.write_all(&msg).await?;
        let mut back = [0u8; 64];
        c.read_exact(&mut back).await?;
        samples.push(t.elapsed().as_secs_f64() * 1000.0);
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let p50 = samples[samples.len() / 2];
    let p95 = samples[(samples.len() * 95) / 100];
    println!(
        "     p50 {p50:.1} ms   p95 {p95:.1} ms   min {:.1} ms   max {:.1} ms",
        samples[0],
        samples[samples.len() - 1]
    );
    println!("     (each sample includes connect + a full ML-KEM + Falcon handshake)");

    // Steady state: one connection, many round trips. This is how a validator
    // actually uses the link, and it is the number that decides whether the
    // relay can carry consensus votes.
    println!();
    println!("  latency, 64-byte round trips on one established connection");
    let mut c = TcpStream::connect(target).await?;
    c.set_nodelay(true)?;
    let msg = [0x5au8; 64];
    let mut back = [0u8; 64];
    // Warm the path so the handshake is not counted in the first sample.
    c.write_all(&msg).await?;
    c.read_exact(&mut back).await?;
    let mut steady = Vec::new();
    for _ in 0..200 {
        let t = Instant::now();
        c.write_all(&msg).await?;
        c.read_exact(&mut back).await?;
        steady.push(t.elapsed().as_secs_f64() * 1000.0);
    }
    steady.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!(
        "     p50 {:.1} ms   p95 {:.1} ms   min {:.1} ms   max {:.1} ms",
        steady[steady.len() / 2],
        steady[(steady.len() * 95) / 100],
        steady[0],
        steady[steady.len() - 1]
    );
    println!(
        "     ({} samples, no handshake, this is the consensus-vote number)",
        steady.len()
    );
    drop(c);

    // Throughput.
    println!();
    println!("  throughput, {mib} MiB echoed through the relay");
    let size = mib * 1024 * 1024;
    let payload: Vec<u8> = (0..size).map(|i| (i % 251) as u8).collect();
    let mut c = TcpStream::connect(target).await?;
    let t = Instant::now();

    let (mut r, mut w) = c.split();
    let send = payload.clone();
    let writer = async move {
        w.write_all(&send).await?;
        Ok::<_, std::io::Error>(())
    };
    let mut echoed = vec![0u8; size];
    let reader = async { r.read_exact(&mut echoed).await };
    let (wr, rd) = tokio::join!(writer, reader);
    wr?;
    rd?;

    let secs = t.elapsed().as_secs_f64();
    println!("     {mib} MiB round trip in {secs:.2} s");
    println!("     {:.1} MiB/s", mib as f64 / secs);
    println!(
        "     payload identical: {}",
        if echoed == payload { "yes" } else { "NO" }
    );
    println!();
    Ok(())
}
