# PQTG relay client image.
#
# Runs `relay_wan` (examples/relay_wan.rs): a post-quantum TCP relay with
# mutual authentication (ML-KEM-768, Falcon-512, pinned identities on both
# sides). Intended as a sidecar next to a service that must reach a remote
# TCP backend over a post-quantum tunnel, for example an RPC endpoint.
#
# Build (from the repository root):
#   docker build -f deploy/relay-client/Dockerfile -t pqtg-relay:local .
#
# The same image serves both roles; the role is the first argument:
#   relay_wan client <listen> <remote> --pin SHA3-256:<b64>
#   relay_wan server <listen> <backend> --client SHA3-256:<b64> [--client ...]
#   relay_wan fingerprint <keyfile>          (creates the identity if missing)
#
# The identity key is read from the working directory (/var/lib/pqtg):
# relay_wan_client.key for the client role, relay_wan_server.key for the
# server role. Mount it as a secret; never bake it into the image.

FROM rust:1-bookworm AS build
WORKDIR /src
COPY . .
RUN cargo build --release --example relay_wan --locked \
    && strip target/release/examples/relay_wan

FROM debian:bookworm-slim
RUN useradd --system --uid 10001 --home /var/lib/pqtg --shell /usr/sbin/nologin pqtg \
    && mkdir -p /var/lib/pqtg && chown pqtg:pqtg /var/lib/pqtg
COPY --from=build /src/target/release/examples/relay_wan /usr/local/bin/relay_wan
USER pqtg
WORKDIR /var/lib/pqtg
ENTRYPOINT ["/usr/local/bin/relay_wan"]
CMD ["--help"]
