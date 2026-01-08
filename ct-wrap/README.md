# CT-Wrap

Quantum-safe data wrapper: post-quantum key encapsulation + AEAD encryption + optional ZK proofs.

This folder is a standalone product sub-project inside `ct-crypto-lean-applied-extended`.

See `ARCHITECTURE.md` for the wrap/unwrap flow and security properties.

## Quick start (dev)

Prereqs:
- Rust toolchain (`cargo`)
- Node.js + npm (for circom/snarkjs proof pipeline)
- `circom` binary (optional; used by `scripts/setup_circuits.sh`)

Commands:
- Build/run API: `cargo run`
- Run unit tests: `cargo test`
- Setup circuits (Groth16): `./scripts/setup_circuits.sh`
- Run ZK e2e smoke test (optional): `cargo test -- --ignored zk_e2e`
- Run API integration test (service must be running): `./scripts/integration_test.sh`

## API

| Endpoint | Method | Purpose |
|----------|--------|---------|
| `/health` | GET | Health check |
| `/api/v1/wrap` | POST | Wrap bytes into a `CTWrapPackage` |
| `/api/v1/unwrap` | POST | Unwrap with recipient keypair |
| `/api/v1/zk/vk/:circuit` | GET | Fetch verification key + VK hash |

Notes:
- PQ primitives are implemented via `pqcrypto-*` crates (Kyber1024/Dilithium5) as ML-KEM/ML-DSA mappings.
- ZK proof generation is currently delegated to Node.js via `scripts/generate_proof.js`.

## ZK circuits (optional)

This repo includes small Circom 2 circuits under `circuits/`.

Prereqs:
- `snarkjs` (installed via `npm install`)
- `circom` compiler (installed separately; not vendored)
- A trusted ptau file (Groth16 setup), e.g. `powersOfTau28_hez_final_16.ptau` in `ct-wrap/`

Setup:

```bash
cd ct-wrap
npm install
# place powersOfTau28_hez_final_16.ptau in this folder
./scripts/setup_circuits.sh
```

Proof generation (default circuit):

```bash
cd ct-wrap
node ./scripts/generate_proof.js --circuit data_commitment --build-dir build/circuits --data-hex deadbeef
```

Verification key API (when running the service):
- `GET /api/v1/zk/vk/:circuit`
