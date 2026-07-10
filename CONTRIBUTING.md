# Contributing to PQ Transport Gateway

Thank you for your interest in PQTG. This project addresses a known vulnerability class in ETSI GS QKD 014 (classical TLS on the control channel). Contribution quality and security hygiene matter.

## Getting started

1. Fork the repository
2. Create a feature branch: `git checkout -b feat/your-change`
3. Make your changes with tests
4. Ensure CI passes locally
5. Open a pull request against `main`

## Legal: Developer Certificate of Origin (DCO)

All commits must be signed off under the [Developer Certificate of Origin](https://developercertificate.org/):

```
git commit -s -m "your message"
```

Commits without a sign-off will be rejected by CI.

## Code standards

- **Formatting:** `cargo fmt --all` must produce no changes
- **Linting:** `cargo clippy --all-targets -- -D warnings` must pass
- **Unsafe code:** Avoid `unsafe` blocks in cryptographic paths. If unavoidable, include a safety comment
- **Lean proofs:** Update the 99 Lean 4 theorems if you change the proven protocol surface

## Testing

- Unit tests: `cargo test --lib`
- Integration tests: `cargo test --test '*'`
- Interop tests against reference QKD hardware where available

## Security-sensitive changes

Any change touching the control-channel protocol, KEM negotiation, or key-derivation is security-sensitive. Tag the PR with `security-review`. Do not open public issues for suspected vulnerabilities — see [SECURITY.md](SECURITY.md).

## Commit messages

Follow [Conventional Commits](https://www.conventionalcommits.org/).

## Review process

- One non-author maintainer must approve before merge
- All required CI checks must pass (build, test, clippy, DCO)

## License

By contributing, you agree that your contributions are licensed under the terms of both [LICENSE-APACHE](LICENSE-APACHE) and [LICENSE-MIT](LICENSE-MIT).
