#!/usr/bin/env bash
set -euo pipefail

CIRCUIT_DIR="circuits"
BUILD_DIR="build/circuits"
PTAU_FILE="powersOfTau28_hez_final_16.ptau"

mkdir -p "$BUILD_DIR"

if ! command -v circom >/dev/null 2>&1; then
  echo "Missing 'circom' compiler in PATH."
  echo "Install circom (v2.x) and re-run."
  exit 1
fi

SNARKJS=(snarkjs)
if ! command -v snarkjs >/dev/null 2>&1; then
  if command -v npx >/dev/null 2>&1; then
    # Prefer the repo-local snarkjs when installed via npm.
    SNARKJS=(npx --no-install snarkjs)
  fi
fi

if ! "${SNARKJS[@]}" --help >/dev/null 2>&1; then
  echo "Missing 'snarkjs' (or npm deps not installed)."
  echo "Run: npm install"
  exit 1
fi

if [ ! -f "$PTAU_FILE" ]; then
  echo "Missing $PTAU_FILE."
  echo "Download it manually (trusted source) and re-run."
  exit 1
fi

setup_circuit() {
  local name=$1
  echo "Setting up circuit: $name"

  circom "$CIRCUIT_DIR/$name.circom" \
    --r1cs \
    --wasm \
    --sym \
    -o "$BUILD_DIR" \
    -l node_modules

  "${SNARKJS[@]}" groth16 setup \
    "$BUILD_DIR/$name.r1cs" \
    "$PTAU_FILE" \
    "$BUILD_DIR/${name}_0000.zkey"

  echo "random-entropy-$(date +%s)" | "${SNARKJS[@]}" zkey contribute \
    "$BUILD_DIR/${name}_0000.zkey" \
    "$BUILD_DIR/${name}_final.zkey" \
    --name="CT-Wrap Setup"

  "${SNARKJS[@]}" zkey export verificationkey \
    "$BUILD_DIR/${name}_final.zkey" \
    "$BUILD_DIR/${name}_verification_key.json"

  "${SNARKJS[@]}" zkey export solidityverifier \
    "$BUILD_DIR/${name}_final.zkey" \
    "$BUILD_DIR/${name}_verifier.sol"

  echo "Circuit $name setup complete"
}

setup_circuit "data_commitment"
setup_circuit "range_commitment"
setup_circuit "merkle_membership"

echo "All circuits setup complete!"
