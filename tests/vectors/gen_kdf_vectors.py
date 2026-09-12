#!/usr/bin/env python3
"""Independent generator for the PQTG key-schedule known-answer vectors.

A second implementation of docs/KEY-SCHEDULE.md written from the document,
not ported from src/kdf.rs. Uses only the standard library (hashlib SHA3-256
and hmac). Rewrites kdf-domains.json, handshake-v3.json and relay-v4.json in
this directory; `cargo test --test kdf_kat` checks the Rust code against them.

The byte-pattern inputs below are not valid keys or ciphertexts, they are only
ever hashed. Nothing here is secret.
"""

import hashlib
import hmac
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = b"PQTG-DOMAIN-TREE-v1"


def sha3(*parts):
    h = hashlib.sha3_256()
    for p in parts:
        h.update(p)
    return h.digest()


def be32(n):
    return n.to_bytes(4, "big")


def be64(n):
    return n.to_bytes(8, "big")


def domain(path):
    d = sha3(ROOT)
    for leaf in path:
        d = sha3(d, be32(len(leaf)), leaf.encode())
    return d


def H(d, parts):
    h = hashlib.sha3_256()
    h.update(d)
    for p in parts:
        h.update(be32(len(p)))
        h.update(p)
    return h.digest()


def PRF(key, d, parts):
    m = d + b"".join(be32(len(p)) + p for p in parts)
    return hmac.new(key, m, hashlib.sha3_256).digest()


def chain_start(d):
    return H(d, [])


def chain_mix(ck, d, x):
    return PRF(ck, d, [x])


def chain_finish(ck, d):
    return PRF(ck, d, [])


ALL = [
    ["gateway", "v3", "transcript"],
    ["gateway", "v3", "client-hello"],
    ["gateway", "v3", "chain"],
    ["gateway", "v3", "mix", "kem"],
    ["gateway", "v3", "mix", "qkd"],
    ["gateway", "v3", "mix", "transcript"],
    ["gateway", "v3", "session-key"],
    ["relay", "v4", "hello"],
    ["relay", "v4", "transcript"],
    ["relay", "v4", "key", "c2s"],
    ["relay", "v4", "key", "s2c"],
    ["relay", "v4", "ratchet"],
]
D = {"/".join(p): domain(p) for p in ALL}
assert len(set(D.values())) == len(D), "two paths share a constant"


def pat(n, a, b):
    return bytes(((i * a + b) & 0xFF) for i in range(n))


client_random = bytes(range(0x00, 0x20))
server_random = bytes(range(0x20, 0x40))
kem_ek = pat(1184, 7, 3)
falcon_pk = pat(897, 13, 5)  # server Falcon-512 vk
kem_ct = pat(1088, 11, 9)
kem_ss = bytes(range(0x40, 0x60))
qkd = bytes(range(0x80, 0xA0))
slh_vk = bytes(range(0xA0, 0xC0))
client_falcon_vk = pat(897, 17, 1)
TS = 1_789_000_000

# --- gateway v3 --------------------------------------------------------------
KEY_ID = b"1e4d1e4d-aaaa-bbbb-cccc-0123456789ab"
t_hybrid = H(
    D["gateway/v3/transcript"],
    [client_random, server_random, kem_ek, falcon_pk, kem_ct, b"\x01", KEY_ID, b"sae-101", be32(32)],
)
t_pqc = H(
    D["gateway/v3/transcript"],
    [client_random, server_random, kem_ek, falcon_pk, kem_ct, b"\x00", b"", b"sae-101", be32(0)],
)
hello = H(
    D["gateway/v3/client-hello"],
    [client_random, be64(TS), kem_ek, falcon_pk, slh_vk, be64(32), b"sae-102", b"\x01"],
)


def v3_key(ss, q, t):
    ck = chain_start(D["gateway/v3/chain"])
    ck = chain_mix(ck, D["gateway/v3/mix/kem"], ss)
    if q is not None:
        ck = chain_mix(ck, D["gateway/v3/mix/qkd"], q)
    ck = chain_mix(ck, D["gateway/v3/mix/transcript"], t)
    return chain_finish(ck, D["gateway/v3/session-key"])


k_pqc = v3_key(kem_ss, None, t_pqc)
k_hyb = v3_key(kem_ss, qkd, t_hybrid)

# --- relay v4 ----------------------------------------------------------------
rh = H(D["relay/v4/hello"], [client_random, be64(TS), kem_ek, client_falcon_vk, slh_vk])
rt = H(D["relay/v4/transcript"], [client_random, server_random, kem_ek, kem_ct, client_falcon_vk, falcon_pk])
c2s = PRF(kem_ss, D["relay/v4/key/c2s"], [rt])
s2c = PRF(kem_ss, D["relay/v4/key/s2c"], [rt])
r1 = PRF(c2s, D["relay/v4/ratchet"], [be32(1), b""])
r2 = PRF(r1, D["relay/v4/ratchet"], [be32(2), kem_ss])


def hx(b):
    return b.hex()


ABOUT = (
    "Generated independently (Python hashlib SHA3-256 + hmac) from docs/KEY-SCHEDULE.md. "
    "Byte-pattern inputs are NOT valid keys, only hashed. Rust: tests/kdf_kat.rs."
)


def dump(name, obj):
    with open(os.path.join(HERE, name), "w") as f:
        json.dump(obj, f, indent=2)
        f.write("\n")


dump(
    "kdf-domains.json",
    {
        "_about": ABOUT,
        "root": "PQTG-DOMAIN-TREE-v1",
        "rule": "D(root)=SHA3(root); D(parent/leaf)=SHA3(D(parent)||be32(len(leaf))||leaf)",
        "domains": {k: hx(v) for k, v in D.items()},
    },
)
dump(
    "handshake-v3.json",
    {
        "_about": ABOUT,
        "inputs": {
            "client_random": hx(client_random),
            "server_random": hx(server_random),
            "client_kem_ek": "byte[i]=(7i+3)&255, 1184 bytes",
            "server_falcon_pk": "byte[i]=(13i+5)&255, 897 bytes",
            "kem_ciphertext": "byte[i]=(11i+9)&255, 1088 bytes",
            "kem_ss": hx(kem_ss),
            "qkd_key": hx(qkd),
            "slh_dsa_vk": hx(slh_vk),
            "timestamp": TS,
            "requested_key_size": 32,
            "client_sae_id": "sae-102",
            "qkd_capable": True,
            "hybrid": {
                "key_mode_byte": 1,
                "qkd_key_id": KEY_ID.decode(),
                "master_sae_id": "sae-101",
                "qkd_key_len": 32,
            },
            "pqc_only": {"key_mode_byte": 0, "qkd_key_id": "", "master_sae_id": "sae-101", "qkd_key_len": 0},
        },
        "expected": {
            "transcript_hybrid": hx(t_hybrid),
            "transcript_pqc_only": hx(t_pqc),
            "client_hello_digest": hx(hello),
            "session_key_pqc_only": hx(k_pqc),
            "session_key_hybrid": hx(k_hyb),
        },
        "chain": (
            "ck=SHA3(D[chain]); ck=HMAC(ck,D[mix/kem]||len||ss); [ck=HMAC(ck,D[mix/qkd]||len||qkd)]; "
            "ck=HMAC(ck,D[mix/transcript]||len||t); key=HMAC(ck,D[session-key])"
        ),
    },
)
dump(
    "relay-v4.json",
    {
        "_about": ABOUT,
        "inputs": {
            "client_random": hx(client_random),
            "server_random": hx(server_random),
            "kem_ek": "byte[i]=(7i+3)&255, 1184 bytes",
            "kem_ct": "byte[i]=(11i+9)&255, 1088 bytes",
            "client_falcon_vk": "byte[i]=(17i+1)&255, 897 bytes",
            "server_falcon_vk": "byte[i]=(13i+5)&255, 897 bytes",
            "slh_dsa_vk": hx(slh_vk),
            "timestamp": TS,
            "kem_ss": hx(kem_ss),
        },
        "expected": {
            "hello_digest": hx(rh),
            "transcript": hx(rt),
            "key_c2s": hx(c2s),
            "key_s2c": hx(s2c),
            "ratchet_epoch1_hash_only_from_c2s": hx(r1),
            "ratchet_epoch2_with_fresh_kem_ss_from_epoch1": hx(r2),
        },
        "rules": {
            "directional_key": "HMAC(kem_ss, D[key/dir]||len||transcript)",
            "ratchet": "HMAC(k_n, D[ratchet]||len(4)||be32(n+1)||len||fresh)",
        },
    },
)
print("wrote kdf-domains.json, handshake-v3.json, relay-v4.json")
