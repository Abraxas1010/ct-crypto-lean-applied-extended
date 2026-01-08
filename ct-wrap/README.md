# CT-Wrap (Private)

Quantum-safe data wrapper: post-quantum key encapsulation + AEAD encryption + optional ZK proofs.

This folder is a standalone product sub-project inside `ct-crypto-lean-private`.

## Quick start (dev)

Prereqs:
- Rust toolchain (`cargo`)
- Node.js + npm (for circom/snarkjs proof pipeline)
- `circom` binary (optional; used by `scripts/setup_circuits.sh`)

Commands:
- Build/run API: `cargo run`
- Run unit tests: `cargo test`
- Setup circuits (Groth16): `./scripts/setup_circuits.sh`

Notes:
- PQ primitives are implemented via `pqcrypto-*` crates (Kyber1024/Dilithium5) as ML-KEM/ML-DSA mappings.
- ZK proof generation is currently delegated to Node.js via `scripts/generate_proof.js`.
