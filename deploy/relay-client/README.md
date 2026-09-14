# PQTG relay client as a sidecar

A post-quantum, mutually authenticated TCP tunnel from a pod to a remote
backend, using the relay mode of PQTG (`examples/relay_wan.rs`, wire
`relay-4`). Typical use: an application that must reach a remote RPC endpoint
keeps talking to `127.0.0.1:<port>`; the sidecar carries that traffic inside
an ML-KEM-768 + Falcon-512 tunnel to a relay server that forwards to the real
backend. Both ends authenticate: the client pins the server's identity, the
server allow-lists the client's.

Files:

- `Dockerfile`: the image (build from the repository root).
- `k8s-sidecar.yaml`: the sidecar container and identity volume to merge into
  an existing Deployment.

## Operator steps (cluster side)

1. **Build or pull the image.** From the repository root:
   `docker build -f deploy/relay-client/Dockerfile -t pqtg-relay:<tag> .`
2. **Generate the identity once, in your cluster.** The private key never
   leaves it; only the fingerprint is shared.
   ```
   docker run --rm -v "$PWD/identity:/var/lib/pqtg" pqtg-relay:<tag> fingerprint relay_wan_client.key
   ```
   This prints `SHA3-256:<base64>` and writes `identity/relay_wan_client.key`.
3. **Send the fingerprint** to the operator of the relay server, who adds it to
   the server's allow-list and sends back the server's own fingerprint and its
   host and port.
4. **Create the secret** from the key file:
   ```
   kubectl -n <ns> create secret generic pqtg-relay-identity --from-file=relay_wan_client.key=identity/relay_wan_client.key
   ```
5. **Add the sidecar** from `k8s-sidecar.yaml` to the application's pod spec,
   filling `IMAGE`, `RELAY_HOST`, `RELAY_PORT`, `SERVER_PIN` and `LISTEN_PORT`.
   Point the application at `http://127.0.0.1:<LISTEN_PORT>` if it is not
   already.
6. **Verify** from inside the pod:
   ```
   curl -s -H 'Content-Type: application/json' -d '{"id":1,"jsonrpc":"2.0","method":"system_health","params":[]}' http://127.0.0.1:<LISTEN_PORT>
   ```
   The sidecar log shows `relay client listening on 127.0.0.1:<port>, tunnelling to <host>:<port>, server pinned to SHA3-256:...` at start.

## What the operator of the relay server does

- Adds the client fingerprint: `relay_wan server <listen> <backend> --client SHA3-256:<client> [--client ...]`
  (one `--client` per authorized client; restart to apply).
- Opens the relay port to the client's egress address(es) only.
- Sends back the server fingerprint printed at startup (`identity fingerprint SHA3-256:... (clients pin this)`).

## Failure modes, all fail closed

- Wrong or missing `--pin`: the client refuses the server before any data.
- Client not on the allow-list: the server refuses the handshake; the
  application sees a closed connection, never plaintext.
- Relay server down: the application sees a closed connection; nothing falls
  back to a direct or classical path.

## Rollback

Remove the sidecar container and point the application back at whatever it
used before. The secret can stay; it is harmless without the allow-list entry.
