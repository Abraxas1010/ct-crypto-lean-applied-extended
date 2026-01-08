#!/usr/bin/env bash
set -euo pipefail

CIRCUIT_DIR="circuits"
BUILD_DIR="build/circuits"
PTAU_FILE="powersOfTau28_hez_final_16.ptau"

mkdir -p "$BUILD_DIR"

if [ ! -f "$PTAU_FILE" ]; then
  echo "Missing $PTAU_FILE."
  echo "Download it manually (trusted source) and re-run."
  exit 1
fi

setup_circuit() {
  local name=$1
  echo "Setting up circuit: $name"

  circom "$CIRCUIT_DIR/$name.circom" \
    --r1cs "$BUILD_DIR/$name.r1cs" \
    --wasm "$BUILD_DIR/${name}_js/${name}.wasm" \
    --sym "$BUILD_DIR/$name.sym" \
    -l node_modules

  snarkjs groth16 setup \
    "$BUILD_DIR/$name.r1cs" \
    "$PTAU_FILE" \
    "$BUILD_DIR/${name}_0000.zkey"

  echo "random-entropy-$(date +%s)" | snarkjs zkey contribute \
    "$BUILD_DIR/${name}_0000.zkey" \
    "$BUILD_DIR/${name}_final.zkey" \
    --name="CT-Wrap Setup"

  snarkjs zkey export verificationkey \
    "$BUILD_DIR/${name}_final.zkey" \
    "$BUILD_DIR/${name}_verification_key.json"

  snarkjs zkey export solidityverifier \
    "$BUILD_DIR/${name}_final.zkey" \
    "$BUILD_DIR/${name}_verifier.sol"

  echo "Circuit $name setup complete"
}

setup_circuit "data_commitment"
setup_circuit "range_commitment"
setup_circuit "merkle_membership"

echo "All circuits setup complete!"
