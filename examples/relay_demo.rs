//! Live demonstration of the post-quantum relay.
//!
//! Stands up a real backend, a relay server and a relay client on loopback,
//! pushes real traffic through, and prints what actually happened: how fast it
//! moved, and what the wire looked like.
//!
//! Run with:
//! ```text
//! cargo run --example relay_demo
//! ```

use anyhow::Result;
use std::sync::Arc;
use std::time::Instant;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

use pq_qkd_proxy::crypto::PqKeyExchange;
use pq_qkd_proxy::relay::{client_handshake, PinPolicy, RelayClient, RelayServer, ServerPin};

/// A backend that echoes whatever it is sent, standing in for a validator's
/// p2p port or any other TCP service.
async fn spawn_echo() -> Result<std::net::SocketAddr> {
    let listener = TcpListener::bind("127.0.0.1:0").await?;
    let addr = listener.local_addr()?;
    tokio::spawn(async move {
        while let Ok((mut s, _)) = listener.accept().await {
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
    });
    Ok(addr)
}

fn hexdump(label: &str, bytes: &[u8], take: usize) {
    let n = take.min(bytes.len());
    print!("  {label:<22}");
    for b in &bytes[..n] {
        print!("{b:02x}");
    }
    println!(" ... ({} bytes total)", bytes.len());
}

#[tokio::main]
async fn main() -> Result<()> {
    println!();
    println!("  PQTG post-quantum relay — live demonstration");
    println!("  ============================================");
    println!();

    // ---- topology ---------------------------------------------------------
    let backend = spawn_echo().await?;
    println!("  backend (plaintext TCP)      {backend}");

    let server_identity = Arc::new(PqKeyExchange::new()?);
    // The pin is what the operator distributes out of band; here the demo
    // simply has the key in hand.
    let server_pin = ServerPin::of(&server_identity);
    let server_listener = TcpListener::bind("127.0.0.1:0").await?;
    let server_addr = server_listener.local_addr()?;
    let server = RelayServer::new(server_identity, backend, 256);
    tokio::spawn(async move {
        let _ = server.serve(server_listener).await;
    });
    println!("  relay server (post-quantum)  {server_addr}  ->  {backend}");
    println!("  server identity pinned as    {server_pin}");

    let client_identity = Arc::new(PqKeyExchange::new()?);
    let client_listener = TcpListener::bind("127.0.0.1:0").await?;
    let client_addr = client_listener.local_addr()?;
    let client = RelayClient::new(client_identity, server_addr, PinPolicy::Require(server_pin));
    tokio::spawn(async move {
        let _ = client.serve(client_listener).await;
    });
    println!("  relay client (plaintext in)  {client_addr}  ->  {server_addr}");
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;

    // ---- 1. handshake cost ------------------------------------------------
    println!();
    println!("  1. Handshake");
    let id = PqKeyExchange::new()?;
    let mut probe = TcpStream::connect(server_addr).await?;
    let t = Instant::now();
    let mut session = client_handshake(&mut probe, &id, PinPolicy::Require(server_pin)).await?;
    let handshake_us = t.elapsed().as_micros();
    println!("     ML-KEM-768 + Falcon-512 over a SHA3-256 transcript");
    println!("     completed in {handshake_us} us");

    // ---- 2. the wire is not plaintext -------------------------------------
    println!();
    println!("  2. What crosses the wire");
    let secret = b"VALIDATOR-VOTE-block-1637745-do-not-let-this-be-readable";
    let record = session.send.seal(secret)?;
    hexdump("plaintext in", secret, 24);
    hexdump("sealed record out", &record, 24);
    let leaked = record.windows(secret.len()).any(|w| w == secret);
    println!(
        "     plaintext present in the sealed record: {}",
        if leaked { "YES — BROKEN" } else { "no" }
    );
    drop(probe);

    // ---- 3. real traffic, end to end --------------------------------------
    println!();
    println!("  3. Traffic through client relay -> server relay -> backend");
    let payload_size = 4 * 1024 * 1024;
    let payload: Vec<u8> = (0..payload_size).map(|i| (i % 251) as u8).collect();

    let mut conn = TcpStream::connect(client_addr).await?;
    let t = Instant::now();

    let to_send = payload.clone();
    let writer = tokio::spawn(async move {
        let (_, mut w) = conn.split();
        let _ = w.write_all(&to_send).await;
        // keep the connection open for the echo to come back
        tokio::time::sleep(std::time::Duration::from_secs(30)).await;
    });

    let mut conn2 = TcpStream::connect(client_addr).await?;
    conn2.write_all(&payload).await?;
    let mut echoed = vec![0u8; payload_size];
    conn2.read_exact(&mut echoed).await?;
    let elapsed = t.elapsed();
    writer.abort();

    let mb = payload_size as f64 / (1024.0 * 1024.0);
    println!(
        "     sent and echoed {mb:.0} MiB in {:.2} s",
        elapsed.as_secs_f64()
    );
    println!(
        "     round trip throughput {:.1} MiB/s",
        mb / elapsed.as_secs_f64()
    );
    println!(
        "     payload identical after the round trip: {}",
        if echoed == payload {
            "yes"
        } else {
            "NO — BROKEN"
        }
    );

    // ---- 4. concurrency ---------------------------------------------------
    println!();
    println!("  4. Concurrent connections, each with its own key schedule");
    let n = 32;
    let t = Instant::now();
    let mut handles = Vec::new();
    for i in 0..n {
        handles.push(tokio::spawn(async move {
            let mut c = TcpStream::connect(client_addr).await.ok()?;
            let msg = vec![i as u8; 4096];
            c.write_all(&msg).await.ok()?;
            let mut back = vec![0u8; msg.len()];
            c.read_exact(&mut back).await.ok()?;
            Some(back == msg)
        }));
    }
    let mut ok = 0;
    for h in handles {
        if matches!(h.await, Ok(Some(true))) {
            ok += 1;
        }
    }
    println!("     {ok} of {n} connections carried their own bytes correctly");
    println!("     established in {:.2} s", t.elapsed().as_secs_f64());
    println!();
    println!("     This is the property the qssh tunnel could not provide:");
    println!("     a full mesh at N >= 4 forced one node to accept two inbound");
    println!("     forwards on the same loopback, and the second always failed.");

    println!();
    println!("  ============================================");
    println!("  ML-KEM-768 key exchange, Falcon-512 authentication,");
    println!("  AES-256-GCM records, SHA3-256 transcript and ratchet.");
    println!("  No classical cryptography anywhere in this path.");
    println!();

    Ok(())
}
