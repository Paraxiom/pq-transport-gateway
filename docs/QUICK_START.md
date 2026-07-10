# PQTG Quick Start Guide

## Build

```bash
cargo build --release
```

## Configure

Edit `config.toml`:

```toml
[proxy]
listen = "192.168.0.100:8443"  # Your QKD machine IP

[qkd]
vendor_api = "https://localhost:443"  # QKD vendor API

[security]
authorized_keys = "/etc/pqtg/authorized_keys"
```

## Run

```bash
./target/release/pq-transport-gateway --config config.toml
```

## Test Connection

From QSSH:
```bash
qssh --qkd --qkd-endpoint "https://qkd-machine:8443" user@host
```

That's it! PQTG now protects your QKD API with post-quantum cryptography.