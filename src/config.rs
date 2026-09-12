//! Configuration management for PQ-QKD-Proxy

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::net::{IpAddr, SocketAddr};
use std::path::Path;

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Config {
    pub proxy: ProxyConfig,
    pub qkd: QkdConfig,
    pub security: SecurityConfig,
    /// Post-quantum TCP relay. Optional and disabled by default, so an existing
    /// gateway deployment is unaffected.
    #[serde(default)]
    pub relay: RelayConfig,
    #[serde(default)]
    pub performance: PerformanceConfig,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct ProxyConfig {
    /// Address to listen on for PQ connections
    pub listen: SocketAddr,

    /// Maximum concurrent connections
    #[serde(default = "default_max_connections")]
    pub max_connections: usize,

    /// Connection timeout in seconds
    #[serde(default = "default_connection_timeout")]
    pub connection_timeout: u64,

    /// Allowed source IP ranges (CIDR notation)
    #[serde(default)]
    pub allowed_sources: Vec<String>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct QkdConfig {
    /// Vendor API endpoint (must be localhost)
    pub vendor_api: String,

    /// Path to vendor certificate
    pub vendor_cert: Option<String>,

    /// Vendor API key
    pub vendor_api_key: Option<String>,

    /// ETSI QKD API version
    #[serde(default = "default_qkd_api_version")]
    pub api_version: String,

    /// Key request timeout in seconds
    #[serde(default = "default_key_timeout")]
    pub key_timeout: u64,

    /// Maximum key size in bytes
    #[serde(default = "default_max_key_size")]
    pub max_key_size: usize,

    /// Default `slave_SAE_ID` used for status checks and the
    /// `get_key(size)` shortcut. ETSI GS QKD 014 v1.1.1 §5.
    #[serde(default = "default_slave_sae_id")]
    pub default_slave_sae_id: String,

    /// Default `master_SAE_ID` used for `get_keys_by_id` lookups.
    #[serde(default = "default_master_sae_id")]
    pub default_master_sae_id: String,

    /// If `true`, validate the vendor's TLS certificate against the
    /// configured `vendor_cert` (and the system trust store if applicable).
    /// If `false` (default), accept self-signed certs — appropriate for
    /// most localhost vendor KMEs that ship with self-signed bundles, but
    /// **not** suitable for production deployments that issue proper certs
    /// to their KME or use mTLS internally. Closes issue #4.
    #[serde(default)]
    pub tls_verify: bool,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct SecurityConfig {
    /// Post-quantum algorithm for key encapsulation
    #[serde(default = "default_pq_algorithm")]
    pub pq_algorithm: String,

    /// Signature algorithm
    #[serde(default = "default_sig_algorithm")]
    pub sig_algorithm: String,

    /// Path to authorized public keys
    pub authorized_keys: String,

    /// Path to proxy's private key
    pub proxy_private_key: String,

    /// Path to proxy's certificate
    pub proxy_certificate: String,

    /// Enable audit logging
    #[serde(default = "default_audit_enabled")]
    pub audit_enabled: bool,

    /// Audit log path
    #[serde(default = "default_audit_log")]
    pub audit_log: String,

    /// Key rotation interval in hours
    #[serde(default = "default_key_rotation_hours")]
    pub key_rotation_hours: u64,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct PerformanceConfig {
    /// Worker threads
    #[serde(default = "default_worker_threads")]
    pub worker_threads: usize,

    /// Request queue size
    #[serde(default = "default_queue_size")]
    pub queue_size: usize,

    /// Enable caching
    #[serde(default = "default_cache_enabled")]
    pub cache_enabled: bool,

    /// Cache TTL in seconds
    #[serde(default = "default_cache_ttl")]
    pub cache_ttl: u64,
}

/// Post-quantum TCP relay.
///
/// PQTG runs as an ETSI-014 gateway, a relay, or both. The relay parses nothing
/// it carries, so it can front any TCP service. Disabled unless `mode` is set.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct RelayConfig {
    /// When true, run ONLY the post-quantum relay and do not start the ETSI-014
    /// gateway (no proxy port bind, no vendor-API check). This is the drop-in
    /// PQ sidecar deployment: front any TCP service, touch nothing else. Default
    /// false so existing gateway deployments are unchanged.
    #[serde(default)]
    pub standalone: bool,

    /// `off` (default), `server`, or `client`.
    ///
    /// `server` accepts post-quantum connections and forwards plaintext to
    /// `backend`. `client` accepts plaintext locally and carries it to a remote
    /// relay server at `remote`.
    #[serde(default = "default_relay_mode")]
    pub mode: String,
    /// Address to listen on.
    #[serde(default)]
    pub listen: Option<SocketAddr>,
    /// Server mode: where decrypted traffic is delivered.
    #[serde(default)]
    pub backend: Option<SocketAddr>,
    /// Client mode: the remote relay server to carry traffic to.
    #[serde(default)]
    pub remote: Option<SocketAddr>,
    /// Server mode: connections relayed at once before new ones are refused.
    #[serde(default = "default_relay_max_connections")]
    pub max_connections: usize,
    /// Client mode: the relay server's identity fingerprint, `SHA3-256:<base64>`
    /// as printed by `--print-fingerprint` on the server. Required unless
    /// `allow_unpinned` is set: without it the client verifies the server's
    /// signature under a key the server itself supplied, which authenticates
    /// nobody (Verifpal finding F2, `formal/VERIFICATION-RESULTS-2026-09-12.md`).
    #[serde(default)]
    pub pin: Option<String>,
    /// Client mode: run without a pin. Every handshake is logged at WARN. For
    /// a bench on a link you already trust; never for a validator.
    #[serde(default)]
    pub allow_unpinned: bool,
    /// Server mode: relay clients allowed to open a tunnel to `backend`, by
    /// identity fingerprint (`SHA3-256:<base64>`, what `--print-fingerprint`
    /// prints on each client). Required unless `allow_any_client` is set: a
    /// relay server that accepts any client is an open door to its backend
    /// (Verifpal finding R1, `formal/RELAY-RESULTS-2026-09-12.md`).
    #[serde(default)]
    pub authorized_clients: Vec<String>,
    /// Server mode: accept any client that signs its hello. Logged at WARN on
    /// every handshake. Only for a backend that authenticates its own peers.
    #[serde(default)]
    pub allow_any_client: bool,
}

fn default_relay_mode() -> String {
    "off".to_string()
}

fn default_relay_max_connections() -> usize {
    256
}

impl Default for RelayConfig {
    fn default() -> Self {
        Self {
            standalone: false,
            mode: default_relay_mode(),
            listen: None,
            backend: None,
            remote: None,
            max_connections: default_relay_max_connections(),
            pin: None,
            allow_unpinned: false,
            authorized_clients: Vec::new(),
            allow_any_client: false,
        }
    }
}

impl RelayConfig {
    pub fn is_enabled(&self) -> bool {
        self.mode != "off"
    }

    /// The client policy for server mode. A non-empty allow-list always wins;
    /// `allow_any_client` only matters when the list is empty.
    pub fn client_policy(&self) -> Result<crate::relay::ClientPolicy> {
        use crate::relay::{ClientPolicy, ServerPin};
        if !self.authorized_clients.is_empty() {
            let list = self
                .authorized_clients
                .iter()
                .map(|s| {
                    ServerPin::parse(s).map_err(|e| {
                        anyhow::anyhow!(
                            "relay.authorized_clients entry {s:?} is not a valid fingerprint: {e}"
                        )
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            return Ok(ClientPolicy::Authorized(list));
        }
        if self.allow_any_client {
            return Ok(ClientPolicy::AnyClient);
        }
        anyhow::bail!(
            "relay.mode = \"server\" requires relay.authorized_clients (each client's fingerprint \
             from `pq-qkd-proxy --print-fingerprint`), or relay.allow_any_client = true only when \
             the backend authenticates its own peers: an open relay exposes the backend to anyone \
             who can reach this port"
        )
    }

    /// The server-identity policy for client mode. A configured pin always
    /// wins; `allow_unpinned` only matters when there is no pin.
    pub fn pin_policy(&self) -> Result<crate::relay::PinPolicy> {
        use crate::relay::{PinPolicy, ServerPin};
        match &self.pin {
            Some(pin) => Ok(PinPolicy::Require(ServerPin::parse(pin).map_err(|e| {
                anyhow::anyhow!("relay.pin is not a valid fingerprint: {e}")
            })?)),
            None if self.allow_unpinned => Ok(PinPolicy::Unpinned),
            None => anyhow::bail!(
                "relay.mode = \"client\" requires relay.pin, the server's fingerprint from \
                 `pq-qkd-proxy --print-fingerprint` (or relay.allow_unpinned = true, only for a \
                 bench on a trusted link: an unpinned client cannot authenticate the server)"
            ),
        }
    }

    /// Reject a relay configuration that cannot work, at startup rather than on
    /// the first connection. A relay that binds and then fails every request is
    /// worse than one that refuses to start.
    pub fn validate(&self) -> Result<()> {
        match self.mode.as_str() {
            "off" => Ok(()),
            "server" => {
                if self.listen.is_none() {
                    anyhow::bail!("relay.mode = \"server\" requires relay.listen");
                }
                if self.backend.is_none() {
                    anyhow::bail!("relay.mode = \"server\" requires relay.backend");
                }
                if self.max_connections == 0 {
                    anyhow::bail!("relay.max_connections must be greater than zero");
                }
                // Refuse a missing or malformed allow-list at startup, not on
                // the first connection.
                self.client_policy().map(|_| ())
            }
            "client" => {
                if self.listen.is_none() {
                    anyhow::bail!("relay.mode = \"client\" requires relay.listen");
                }
                if self.remote.is_none() {
                    anyhow::bail!("relay.mode = \"client\" requires relay.remote");
                }
                // Refuse a missing or malformed pin at startup, not on the
                // first connection.
                self.pin_policy().map(|_| ())
            }
            other => anyhow::bail!(
                "relay.mode must be \"off\", \"server\" or \"client\", got \"{other}\""
            ),
        }
    }
}

impl Config {
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        let content = std::fs::read_to_string(path).context("Failed to read configuration file")?;

        let config: Config = toml::from_str(&content).context("Failed to parse configuration")?;

        config.validate()?;

        Ok(config)
    }

    pub fn validate(&self) -> Result<()> {
        self.relay.validate()?;

        // Ensure vendor API is localhost only
        if !self.qkd.vendor_api.contains("localhost")
            && !self.qkd.vendor_api.contains("127.0.0.1")
            && !self.qkd.vendor_api.contains("::1")
        {
            anyhow::bail!("QKD vendor API must be on localhost for security");
        }

        // Validate algorithms
        match self.security.pq_algorithm.as_str() {
            "falcon512" => {}
            _ => anyhow::bail!("Unsupported PQ algorithm: {}", self.security.pq_algorithm),
        }

        match self.security.sig_algorithm.as_str() {
            "sphincsplus" | "sphincs+" => {}
            _ => anyhow::bail!(
                "Unsupported signature algorithm: {}",
                self.security.sig_algorithm
            ),
        }

        // Check paths exist
        if !Path::new(&self.security.authorized_keys).exists() {
            anyhow::bail!(
                "Authorized keys file not found: {}",
                self.security.authorized_keys
            );
        }

        Ok(())
    }

    /// Is this peer permitted to connect?
    ///
    /// An empty `allowed_sources` means no restriction, which is the documented
    /// default. A NON-empty list is now actually enforced: until 2026-09-08 this
    /// returned `true` unconditionally behind a TODO while being wired into the
    /// accept loop, so every operator who configured an allowlist believed they
    /// had one and did not. It failed open.
    ///
    /// Accepts bare addresses (`10.0.0.5`, `2001:db8::1`) and CIDR blocks
    /// (`10.0.0.0/8`, `2001:db8::/32`). An entry that does not parse is refused
    /// rather than ignored, so a typo cannot silently widen access.
    pub fn is_allowed_source(&self, addr: &SocketAddr) -> bool {
        if self.proxy.allowed_sources.is_empty() {
            return true;
        }
        self.proxy
            .allowed_sources
            .iter()
            .any(|entry| source_matches(entry, addr.ip()))
    }
}

/// Does one allowlist entry cover this address?
///
/// Returns false for anything that does not parse. A malformed entry must never
/// widen access: an operator who writes `10.0.0.0/33` should lose that rule, not
/// gain a wildcard.
fn source_matches(entry: &str, ip: IpAddr) -> bool {
    let entry = entry.trim();
    if entry.is_empty() {
        return false;
    }

    let (net_str, prefix_str) = match entry.split_once('/') {
        Some((n, p)) => (n, Some(p)),
        None => (entry, None),
    };

    let Ok(net) = net_str.parse::<IpAddr>() else {
        return false;
    };

    // A bare address is an exact match. Mixing families never matches.
    let Some(prefix_str) = prefix_str else {
        return net == ip;
    };
    let Ok(prefix) = prefix_str.parse::<u8>() else {
        return false;
    };

    match (net, ip) {
        (IpAddr::V4(net), IpAddr::V4(ip)) => {
            if prefix > 32 {
                return false;
            }
            prefix_match(&net.octets(), &ip.octets(), prefix)
        }
        (IpAddr::V6(net), IpAddr::V6(ip)) => {
            if prefix > 128 {
                return false;
            }
            prefix_match(&net.octets(), &ip.octets(), prefix)
        }
        // An IPv4 rule does not cover an IPv6 peer, or the reverse.
        _ => false,
    }
}

/// Compare the first `prefix` bits of two addresses.
fn prefix_match(net: &[u8], ip: &[u8], prefix: u8) -> bool {
    let whole = (prefix / 8) as usize;
    let bits = prefix % 8;
    if net[..whole] != ip[..whole] {
        return false;
    }
    if bits == 0 {
        return true;
    }
    let mask = 0xffu8 << (8 - bits);
    net[whole] & mask == ip[whole] & mask
}

impl Default for Config {
    fn default() -> Self {
        Self {
            proxy: ProxyConfig {
                listen: ([127, 0, 0, 1], 8443).into(),
                max_connections: default_max_connections(),
                connection_timeout: default_connection_timeout(),
                allowed_sources: vec![],
            },
            qkd: QkdConfig {
                vendor_api: "https://localhost:8080".to_string(),
                vendor_cert: None,
                vendor_api_key: None,
                api_version: default_qkd_api_version(),
                key_timeout: default_key_timeout(),
                max_key_size: default_max_key_size(),
                default_slave_sae_id: default_slave_sae_id(),
                default_master_sae_id: default_master_sae_id(),
                tls_verify: false,
            },
            relay: RelayConfig::default(),
            security: SecurityConfig {
                pq_algorithm: default_pq_algorithm(),
                sig_algorithm: default_sig_algorithm(),
                authorized_keys: "/etc/pq-qkd-proxy/authorized_keys".to_string(),
                proxy_private_key: "/etc/pq-qkd-proxy/proxy.key".to_string(),
                proxy_certificate: "/etc/pq-qkd-proxy/proxy.cert".to_string(),
                audit_enabled: default_audit_enabled(),
                audit_log: default_audit_log(),
                key_rotation_hours: default_key_rotation_hours(),
            },
            performance: PerformanceConfig::default(),
        }
    }
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            worker_threads: default_worker_threads(),
            queue_size: default_queue_size(),
            cache_enabled: default_cache_enabled(),
            cache_ttl: default_cache_ttl(),
        }
    }
}

// Default value functions
fn default_max_connections() -> usize {
    100
}
fn default_connection_timeout() -> u64 {
    30
}
fn default_qkd_api_version() -> String {
    "1.1.1".to_string()
}
fn default_key_timeout() -> u64 {
    5
}
fn default_max_key_size() -> usize {
    1024 * 1024
} // 1MB
fn default_slave_sae_id() -> String {
    "default-slave".to_string()
}
fn default_master_sae_id() -> String {
    "default-master".to_string()
}
fn default_pq_algorithm() -> String {
    "falcon512".to_string()
}
fn default_sig_algorithm() -> String {
    "sphincsplus".to_string()
}
fn default_audit_enabled() -> bool {
    true
}
fn default_audit_log() -> String {
    "/var/log/pq-qkd-proxy/audit.log".to_string()
}
fn default_key_rotation_hours() -> u64 {
    24
}
fn default_worker_threads() -> usize {
    4
}
fn default_queue_size() -> usize {
    1000
}
fn default_cache_enabled() -> bool {
    true
}
fn default_cache_ttl() -> u64 {
    300
} // 5 minutes

#[cfg(test)]
mod allowlist_and_relay_tests {
    use super::*;

    /// A config written before the [relay] section existed must still parse,
    /// with the relay off. If this breaks, every deployed gateway fails to
    /// start on upgrade.
    #[test]
    fn a_config_without_a_relay_section_still_parses() {
        let toml_src = r#"
[proxy]
listen = "127.0.0.1:8443"

[qkd]
vendor_api = "https://localhost:8080"
default_slave_sae_id = "sae-b"
default_master_sae_id = "sae-a"

[security]
pq_algorithm = "falcon512"
sig_algorithm = "sphincsplus"
authorized_keys = "/etc/pq-qkd-proxy/authorized_keys"
proxy_private_key = "/etc/pq-qkd-proxy/proxy.key"
proxy_certificate = "/etc/pq-qkd-proxy/proxy.crt"
audit_log = "/var/log/pq-qkd-proxy/audit.log"

[performance]
"#;
        let cfg: Config = toml::from_str(toml_src).expect("legacy config must parse");
        assert!(!cfg.relay.is_enabled(), "the relay must default to OFF");
    }

    fn sock(s: &str) -> SocketAddr {
        format!("{s}:9999").parse().unwrap()
    }
    fn v6(s: &str) -> SocketAddr {
        format!("[{s}]:9999").parse().unwrap()
    }

    fn cfg_with_sources(sources: &[&str]) -> Config {
        let mut c = Config::default();
        c.proxy.allowed_sources = sources.iter().map(|s| s.to_string()).collect();
        c
    }

    // ---- the bug this replaced -------------------------------------------

    #[test]
    fn a_configured_allowlist_actually_excludes() {
        // Until 2026-09-08 this returned true unconditionally, so every
        // operator who configured an allowlist had none. This is the
        // regression test for that.
        let c = cfg_with_sources(&["10.0.0.0/8"]);
        assert!(c.is_allowed_source(&sock("10.1.2.3")));
        assert!(
            !c.is_allowed_source(&sock("192.168.1.1")),
            "an address outside every rule must be refused"
        );
    }

    #[test]
    fn an_empty_allowlist_still_means_no_restriction() {
        let c = cfg_with_sources(&[]);
        assert!(c.is_allowed_source(&sock("203.0.113.7")));
    }

    // ---- matching --------------------------------------------------------

    #[test]
    fn a_bare_address_is_an_exact_match() {
        let c = cfg_with_sources(&["203.0.113.7"]);
        assert!(c.is_allowed_source(&sock("203.0.113.7")));
        assert!(!c.is_allowed_source(&sock("203.0.113.8")));
    }

    #[test]
    fn cidr_boundaries_are_respected_on_non_byte_prefixes() {
        // /12 is the case a byte-wise comparison gets wrong.
        let c = cfg_with_sources(&["172.16.0.0/12"]);
        assert!(c.is_allowed_source(&sock("172.16.0.1")));
        assert!(c.is_allowed_source(&sock("172.31.255.254")));
        assert!(
            !c.is_allowed_source(&sock("172.32.0.1")),
            "172.32.0.1 is outside 172.16.0.0/12"
        );
        assert!(!c.is_allowed_source(&sock("172.15.255.255")));
    }

    #[test]
    fn a_zero_prefix_matches_everything_in_its_family() {
        let c = cfg_with_sources(&["0.0.0.0/0"]);
        assert!(c.is_allowed_source(&sock("1.2.3.4")));
        assert!(
            !c.is_allowed_source(&v6("2001:db8::1")),
            "an IPv4 rule must not cover an IPv6 peer"
        );
    }

    #[test]
    fn ipv6_is_matched_and_families_do_not_mix() {
        let c = cfg_with_sources(&["2001:db8::/32"]);
        assert!(c.is_allowed_source(&v6("2001:db8::1")));
        assert!(c.is_allowed_source(&v6("2001:db8:ffff::9")));
        assert!(!c.is_allowed_source(&v6("2001:db9::1")));
        assert!(
            !c.is_allowed_source(&sock("10.0.0.1")),
            "an IPv6 rule must not cover an IPv4 peer"
        );
    }

    #[test]
    fn several_rules_are_a_union() {
        let c = cfg_with_sources(&["10.0.0.0/8", "203.0.113.7", "2001:db8::/32"]);
        assert!(c.is_allowed_source(&sock("10.9.9.9")));
        assert!(c.is_allowed_source(&sock("203.0.113.7")));
        assert!(c.is_allowed_source(&v6("2001:db8::5")));
        assert!(!c.is_allowed_source(&sock("8.8.8.8")));
    }

    // ---- malformed entries must never widen access -----------------------

    #[test]
    fn a_malformed_entry_is_refused_rather_than_ignored() {
        // The dangerous failure would be treating an unparseable rule as a
        // wildcard. Each of these must match nothing.
        for bad in [
            "10.0.0.0/33",    // prefix too long for v4
            "2001:db8::/129", // prefix too long for v6
            "not-an-address",
            "10.0.0.0/abc",
            "",
            "   ",
        ] {
            let c = cfg_with_sources(&[bad]);
            assert!(
                !c.is_allowed_source(&sock("10.0.0.1")),
                "malformed entry {bad:?} must not admit anything"
            );
        }
    }

    #[test]
    fn one_bad_rule_does_not_disable_the_good_ones() {
        let c = cfg_with_sources(&["nonsense/99", "10.0.0.0/8"]);
        assert!(c.is_allowed_source(&sock("10.0.0.1")));
        assert!(!c.is_allowed_source(&sock("8.8.8.8")));
    }

    // ---- relay config ----------------------------------------------------

    #[test]
    fn relay_is_off_by_default_and_a_legacy_config_still_parses() {
        let c = Config::default();
        assert!(!c.relay.is_enabled());
        assert!(c.relay.validate().is_ok());
    }

    #[test]
    fn server_mode_requires_listen_and_backend() {
        let mut r = RelayConfig {
            standalone: false,
            mode: "server".into(),
            ..Default::default()
        };
        assert!(r.validate().is_err(), "no listen, no backend");
        r.listen = Some(sock("127.0.0.1"));
        assert!(r.validate().is_err(), "still no backend");
        r.backend = Some(sock("127.0.0.1"));
        assert!(r.validate().is_err(), "still no client allow-list");
        r.allow_any_client = true;
        assert!(r.validate().is_ok());
    }

    // ---- relay server client allow-list (Verifpal R1) ---------------------

    fn server_cfg() -> RelayConfig {
        RelayConfig {
            standalone: false,
            mode: "server".into(),
            listen: Some(sock("127.0.0.1")),
            backend: Some(sock("127.0.0.1")),
            ..Default::default()
        }
    }

    #[test]
    fn a_server_without_an_allow_list_is_refused_at_startup() {
        // The open relay is the R1 configuration. It must not start by
        // default, and the error must tell the operator what to do.
        let err = server_cfg().validate().unwrap_err().to_string();
        assert!(err.contains("relay.authorized_clients"), "got: {err}");
        assert!(err.contains("print-fingerprint"), "got: {err}");
    }

    #[test]
    fn a_server_with_a_valid_allow_list_starts_and_enforces_it() {
        let mut r = server_cfg();
        r.authorized_clients = vec![test_pin(), test_pin()];
        assert!(r.validate().is_ok());
        match r.client_policy().expect("policy") {
            crate::relay::ClientPolicy::Authorized(list) => assert_eq!(list.len(), 2),
            other => panic!("expected Authorized, got {other:?}"),
        }
    }

    #[test]
    fn a_malformed_allow_list_entry_is_refused_at_startup() {
        for bad in ["", "SHA3-256:", "SHA3-256:AAAA", "deadbeef"] {
            let mut r = server_cfg();
            r.authorized_clients = vec![test_pin(), bad.into()];
            let err = r.validate().unwrap_err().to_string();
            assert!(
                err.contains("relay.authorized_clients"),
                "{bad:?}: got: {err}"
            );
        }
    }

    #[test]
    fn allow_any_client_is_an_explicit_opt_out() {
        let mut r = server_cfg();
        r.allow_any_client = true;
        assert!(r.validate().is_ok());
        assert!(matches!(
            r.client_policy().expect("policy"),
            crate::relay::ClientPolicy::AnyClient
        ));
        // A non-empty allow-list wins over the opt-out.
        r.authorized_clients = vec![test_pin()];
        assert!(matches!(
            r.client_policy().expect("policy"),
            crate::relay::ClientPolicy::Authorized(_)
        ));
    }

    #[test]
    fn client_mode_requires_listen_and_remote() {
        let mut r = RelayConfig {
            standalone: false,
            mode: "client".into(),
            pin: Some(test_pin()),
            ..Default::default()
        };
        assert!(r.validate().is_err());
        r.listen = Some(sock("127.0.0.1"));
        assert!(r.validate().is_err(), "still no remote");
        r.remote = Some(sock("127.0.0.1"));
        assert!(r.validate().is_ok());
    }

    // ---- relay client pin (Verifpal F2) ----------------------------------

    /// A syntactically valid fingerprint for config tests: the pin of a fresh
    /// identity, in the exact form `--print-fingerprint` prints.
    fn test_pin() -> String {
        let id = crate::crypto::PqKeyExchange::new().expect("identity");
        crate::crypto::format_fingerprint(&id.identity_fingerprint())
    }

    fn client_cfg() -> RelayConfig {
        RelayConfig {
            standalone: false,
            mode: "client".into(),
            listen: Some(sock("127.0.0.1")),
            remote: Some(sock("127.0.0.1")),
            ..Default::default()
        }
    }

    #[test]
    fn a_client_without_a_pin_is_refused_at_startup() {
        // The unpinned client is the F2 configuration. It must not start by
        // default, and the error must tell the operator what to do.
        let err = client_cfg().validate().unwrap_err().to_string();
        assert!(err.contains("relay.pin"), "got: {err}");
        assert!(err.contains("print-fingerprint"), "got: {err}");
    }

    #[test]
    fn a_client_with_a_pin_starts_and_requires_it() {
        let mut r = client_cfg();
        r.pin = Some(test_pin());
        assert!(r.validate().is_ok());
        assert!(matches!(
            r.pin_policy().expect("policy"),
            crate::relay::PinPolicy::Require(_)
        ));
    }

    #[test]
    fn a_malformed_pin_is_refused_at_startup() {
        for bad in ["", "SHA3-256:", "SHA3-256:AAAA", "deadbeef"] {
            let mut r = client_cfg();
            r.pin = Some(bad.into());
            let err = r.validate().unwrap_err().to_string();
            assert!(err.contains("relay.pin"), "{bad:?}: got: {err}");
        }
    }

    #[test]
    fn allow_unpinned_is_an_explicit_opt_out() {
        let mut r = client_cfg();
        r.allow_unpinned = true;
        assert!(r.validate().is_ok());
        assert!(matches!(
            r.pin_policy().expect("policy"),
            crate::relay::PinPolicy::Unpinned
        ));
        // A pin, when present, wins over the opt-out.
        r.pin = Some(test_pin());
        assert!(matches!(
            r.pin_policy().expect("policy"),
            crate::relay::PinPolicy::Require(_)
        ));
    }

    #[test]
    fn an_unknown_relay_mode_is_refused_at_startup() {
        let r = RelayConfig {
            standalone: false,
            mode: "proxy".into(),
            ..Default::default()
        };
        let err = r.validate().unwrap_err().to_string();
        assert!(err.contains("relay.mode"), "got: {err}");
    }

    #[test]
    fn zero_max_connections_is_refused() {
        // A relay that accepts nothing would bind and then refuse every peer.
        let r = RelayConfig {
            standalone: false,
            mode: "server".into(),
            listen: Some(sock("127.0.0.1")),
            backend: Some(sock("127.0.0.1")),
            max_connections: 0,
            ..Default::default()
        };
        assert!(r.validate().is_err());
    }
}
