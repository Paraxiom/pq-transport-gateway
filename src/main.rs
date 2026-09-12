//! PQTG: Post-quantum secure proxy for QKD hardware APIs.

use anyhow::Result;
use std::path::Path;
use std::sync::Arc;
use tokio::net::TcpListener;
use tracing::{error, info, warn};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

mod audit;
mod auth;
mod config;
mod crypto;
mod proxy;
mod qkd_client;
mod relay;
mod replay;

use config::Config;
use proxy::ProxyServer;

#[tokio::main]
async fn main() -> Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 1 && args[1] == "--generate-keys" {
        return generate_proxy_keys();
    }
    if args.len() > 1 && args[1] == "--print-fingerprint" {
        return print_identity_fingerprint();
    }

    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "pq_qkd_proxy=info,tower=warn".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    info!("Starting PQTG v{}", env!("CARGO_PKG_VERSION"));

    let config_path = std::env::var("PQ_QKD_PROXY_CONFIG")
        .unwrap_or_else(|_| "/etc/pq-qkd-proxy/config.toml".to_string());
    let config = Config::load(&config_path)?;
    let config = Arc::new(config);
    info!("Loaded configuration from {}", config_path);

    // Standalone relay: a drop-in post-quantum sidecar in front of any TCP
    // service, with no ETSI-014 gateway. It binds no proxy port and never calls
    // a QKD vendor, so a chain can put it in front of validator or RPC traffic
    // without running (or configuring) the gateway half at all.
    if config.relay.is_enabled() && config.relay.standalone {
        info!("PQTG relay standalone mode (no ETSI-014 gateway)");
        spawn_relay(config.clone())?;
        // Park forever; the relay runs in its own task.
        loop {
            tokio::time::sleep(tokio::time::Duration::from_secs(3600)).await;
        }
    }

    audit::init(&config.security.audit_log)?;
    audit::log_startup(&config);

    // Relay mode runs alongside the ETSI-014 gateway, not instead of it. A
    // deployment can front QKD key delivery, relay arbitrary TCP, or both.
    if config.relay.is_enabled() {
        spawn_relay(config.clone())?;
    }

    let proxy = ProxyServer::new(config.clone()).await?;
    let listener = TcpListener::bind(&config.proxy.listen).await?;
    info!("PQTG listening on {}", config.proxy.listen);

    proxy.check_vendor_api().await?;

    loop {
        match listener.accept().await {
            Ok((stream, addr)) => {
                info!("New connection from {}", addr);
                if !config.is_allowed_source(&addr) {
                    warn!("Rejected connection from unauthorized address: {}", addr);
                    continue;
                }
                let proxy = proxy.clone();
                tokio::spawn(async move {
                    if let Err(e) = proxy.handle_connection(stream, addr).await {
                        error!("Connection error from {}: {}", addr, e);
                    }
                });
            }
            Err(e) => {
                error!("Accept error: {}", e);
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        }
    }
}

/// Start the post-quantum relay in whichever mode the config selects.
///
/// The relay uses the SAME appliance identity as the gateway, so a client that
/// has pinned this appliance's fingerprint recognises it on either path. The
/// config was validated at load, so the unwraps below cannot fire.
fn spawn_relay(config: Arc<Config>) -> Result<()> {
    use crate::crypto::PqKeyExchange;
    use crate::relay::{RelayClient, RelayServer};

    let identity = Arc::new(
        PqKeyExchange::load_if_present(&config.security.proxy_private_key)?.ok_or_else(|| {
            anyhow::anyhow!(
                "relay is enabled but there is no persisted identity at {}. \
                 Run --generate-keys first: a relay that regenerates its identity \
                 on every restart cannot be pinned by its peers.",
                config.security.proxy_private_key
            )
        })?,
    );

    let listen = config.relay.listen.expect("validated at config load");

    match config.relay.mode.as_str() {
        "server" => {
            let backend = config.relay.backend.expect("validated at config load");
            let max = config.relay.max_connections;
            // Validated at config load too; parsed again here so the policy
            // handed to the server is the one the operator wrote.
            let clients = config.relay.client_policy()?;
            tokio::spawn(async move {
                let listener = match TcpListener::bind(listen).await {
                    Ok(l) => l,
                    Err(e) => {
                        error!("relay could not bind {listen}: {e}");
                        return;
                    }
                };
                let server = RelayServer::new(identity, backend, max, clients);
                if let Err(e) = server.serve(listener).await {
                    error!("relay server exited: {e}");
                }
            });
            info!("relay: server mode, {listen} -> {backend}");
        }
        "client" => {
            let remote = config.relay.remote.expect("validated at config load");
            // Validated at config load too, but parse again here so the policy
            // handed to the client is the one the operator wrote, not a default.
            let policy = config.relay.pin_policy()?;
            tokio::spawn(async move {
                let listener = match TcpListener::bind(listen).await {
                    Ok(l) => l,
                    Err(e) => {
                        error!("relay client could not bind {listen}: {e}");
                        return;
                    }
                };
                let client = RelayClient::new(identity, remote, policy);
                if let Err(e) = client.serve(listener).await {
                    error!("relay client exited: {e}");
                }
            });
            info!("relay: client mode, {listen} -> {remote}");
        }
        other => anyhow::bail!(
            "unreachable relay mode {other}: config validation should have caught this"
        ),
    }
    Ok(())
}

/// Print the identity fingerprint for vk pinning (issue #2).
/// Emits `SHA3-256:<base64-no-pad>` to stdout — distribute this string
/// out-of-band to authorized clients so they can pin the legitimate
/// PQTG and reject MITM substitution.
fn print_identity_fingerprint() -> Result<()> {
    use crate::crypto::{format_fingerprint, PqKeyExchange};

    let key_path = std::env::var("PQTG_IDENTITY_KEY")
        .unwrap_or_else(|_| "/etc/pq-qkd-proxy/proxy.key".to_string());

    let identity = PqKeyExchange::load_if_present(&key_path)?.ok_or_else(|| {
        anyhow::anyhow!("No identity at {}. Run --generate-keys first.", key_path)
    })?;

    let fp = identity.identity_fingerprint();
    let formatted = format_fingerprint(&fp);
    println!("{}", formatted);
    eprintln!();
    eprintln!("Distribute this fingerprint to clients out-of-band.");
    eprintln!("Clients pin it and reject any handshake whose ServerHello");
    eprintln!("does not produce a matching SHA3-256 of (falcon_vk || slh_dsa_vk).");
    eprintln!("See docs/CLIENT-INTEGRATION.md for the pinning protocol.");
    Ok(())
}

/// Generate long-lived proxy identity (Falcon-512 + SLH-DSA-Shake128f).
/// Persists both signing and verification key material to
/// `/etc/pq-qkd-proxy/proxy.key` (0o600) and a public bundle to
/// `proxy.pub` (0o644). ML-KEM keys remain ephemeral per handshake.
///
/// If `proxy.key` already exists the function refuses to overwrite —
/// regenerating identity invalidates every client's pinned trust anchor.
/// Operators must explicitly delete the existing file to force rotation.
fn generate_proxy_keys() -> Result<()> {
    use crate::crypto::PqKeyExchange;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    // Respect PQTG_IDENTITY_KEY so the appliance can be provisioned without root
    // (the loader already honours it). generate-keys used to hardcode /etc, so a
    // non-root deploy could never create an identity — a real deployment bug for
    // a drop-in sidecar. The directory of the key path is created below.
    let key_path = std::env::var("PQTG_IDENTITY_KEY")
        .unwrap_or_else(|_| "/etc/pq-qkd-proxy/proxy.key".to_string());
    let base_dir = Path::new(&key_path)
        .parent()
        .map(|p| p.to_string_lossy().into_owned())
        .unwrap_or_else(|| "/etc/pq-qkd-proxy".to_string());
    let cert_path = format!("{base_dir}/proxy.pub");
    let auth_keys_path = format!("{base_dir}/authorized_keys");

    if Path::new(&key_path).exists() {
        return Err(anyhow::anyhow!(
            "Identity already exists at {}; refusing to overwrite. \
             Delete the file explicitly to force rotation (this invalidates \
             every client's pinned vk).",
            key_path
        ));
    }

    println!("Generating PQTG identity (Falcon-512 + SLH-DSA-Shake128f)...");

    let kex = PqKeyExchange::new()?;

    // Persist signing + verification keys (issue #3).
    fs::create_dir_all(&base_dir)?;
    kex.save(&key_path)?;

    // Public bundle for distribution to clients (for vk pinning, issue #2).
    let mut public_bundle = Vec::with_capacity(929);
    public_bundle.extend_from_slice(kex.falcon_pk_bytes());
    public_bundle.extend_from_slice(kex.slh_dsa_pk_bytes());
    fs::write(&cert_path, &public_bundle)?;
    let mut perms = fs::metadata(&cert_path)?.permissions();
    perms.set_mode(0o644);
    fs::set_permissions(&cert_path, perms)?;

    if !Path::new(&auth_keys_path).exists() {
        let template = r#"# PQTG Authorized Keys
# Format: algorithm base64(falcon_vk(897) || slh_dsa_shake128f_vk(32)) permissions comment
#
# Example:
# falcon512+slh-dsa-shake128f <base64-encoded-public-keys> perm=read,write client@example.com
"#;
        fs::write(&auth_keys_path, template)?;
        let mut perms = fs::metadata(&auth_keys_path)?.permissions();
        perms.set_mode(0o600);
        fs::set_permissions(&auth_keys_path, perms)?;
    }

    println!("Identity (signing + verify):   {}", key_path);
    println!("Public verify bundle:          {}", cert_path);
    println!("Authorized keys template:      {}", auth_keys_path);
    println!();
    println!("Identity will be loaded on next startup. Distribute the public");
    println!("bundle (proxy.pub) to clients out-of-band for vk pinning.");

    Ok(())
}
