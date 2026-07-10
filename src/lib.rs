//! PQTG: Post-Quantum Transport Gateway for QKD infrastructure.
//!
//! Post-quantum primitives come from `paraxiom-pqc` (pure Rust). The gateway
//! sits on the QKD hardware, exposes a quantum-safe API to clients, and
//! translates internally to the vendor's classical TLS API on localhost.

pub mod audit;
pub mod auth;
pub mod config;
pub mod crypto;
pub mod proxy;
pub mod qkd_client;

pub use auth::Authenticator as AuthManager;
pub use config::Config as ProxyConfig;
pub use crypto::{EphemeralKemKey, PqKeyExchange, PqSession};
pub use proxy::{ClientHello, ProxyServer, ServerHello};
pub use qkd_client::QkdClient;

pub type Result<T> = anyhow::Result<T>;
