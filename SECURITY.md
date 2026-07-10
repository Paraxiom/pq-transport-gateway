# Security Policy

## Reporting a vulnerability

Please do **not** open public GitHub issues for suspected vulnerabilities.

Report privately via one of these channels:

1. **Email:** sylvain@paraxiom.org
2. **GitHub Security Advisories:** use the Security tab of this repository

### What to include

- Description of the vulnerability
- Steps to reproduce
- Potential impact
- Suggested fix (if available)

### Response timeframe

- **Initial acknowledgement:** within 48 hours
- **Status update:** within 7 days
- **Resolution target:** within 30 days for critical issues

### Disclosure process

We follow coordinated disclosure. Because PQTG addresses a known class of vulnerability in ETSI GS QKD 014 (classical TLS on the control channel), we coordinate with affected QKD vendors and standards bodies before public disclosure of any additional findings.

1. Reporter submits privately
2. We acknowledge and investigate
3. We coordinate with affected parties where relevant
4. We develop and test a fix
5. We release the fix and publish an advisory
6. We publicly disclose after users have had reasonable time to update

## Scope

### In scope

- Control-channel protocol security (replacing classical TLS in ETSI 014)
- KEM negotiation logic
- Authenticated key material delivery
- Session key derivation

### Out of scope

- Vulnerabilities in upstream QKD hardware (report to vendor)
- Classical TLS hole in ETSI GS QKD 014 itself — that is the **motivating threat**, not a PQTG bug. See Zenodo DOI 10.5281/zenodo.18786526

## Security properties

- Written in Rust for memory safety
- 99 Lean 4 theorems
- NIST-standardized PQC: ML-KEM for key encapsulation, ML-DSA / SLH-DSA for signatures
- Designed as a drop-in replacement for the classical TLS layer in ETSI GS QKD 014 deployments

## Known limitations

- Pre-1.0 software — use with appropriate caution for production QKD links
- Not yet externally audited
- Assumes trusted QKD hardware upstream; PQTG secures the control channel, not the quantum channel itself
