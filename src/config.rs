//! Configuration management for PQ-QKD-Proxy

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::path::Path;

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Config {
    pub proxy: ProxyConfig,
    pub qkd: QkdConfig,
    pub security: SecurityConfig,
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

impl Config {
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self> {
        let content = std::fs::read_to_string(path).context("Failed to read configuration file")?;

        let config: Config = toml::from_str(&content).context("Failed to parse configuration")?;

        config.validate()?;

        Ok(config)
    }

    pub fn validate(&self) -> Result<()> {
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

    pub fn is_allowed_source(&self, _addr: &SocketAddr) -> bool {
        if self.proxy.allowed_sources.is_empty() {
            // No restrictions
            return true;
        }

        // Check against allowed sources
        // TODO: Implement CIDR matching
        true
    }
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
