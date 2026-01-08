#!/usr/bin/env bash
set -euo pipefail

# Integration test: exercises wrap/unwrap and (optionally) ZK-related endpoints via API.
#
# Expected usage:
#   (1) Start the service in another terminal:
#       source ~/.cargo/env && cargo run
#   (2) Run:
#       ./scripts/integration_test.sh

BASE_URL="${BASE_URL:-http://127.0.0.1:3000}"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

need() {
  command -v "$1" >/dev/null 2>&1 || { echo "Missing required tool: $1"; exit 1; }
}

need curl
need base64
need python3

echo "=== CT-Wrap Integration Test ==="

cd "$ROOT"

echo "[1/6] Health check..."
for _ in $(seq 1 20); do
  if curl -sf "$BASE_URL/health" | grep -q "ok"; then
    echo "  OK"
    break
  fi
  sleep 0.25
done
curl -sf "$BASE_URL/health" | grep -q "ok" || { echo "FAIL: health"; exit 1; }

echo "[2/6] Generating ML-KEM keypair..."
if command -v cargo >/dev/null 2>&1; then
  # shellcheck disable=SC1091
  source "${HOME}/.cargo/env" 2>/dev/null || true
fi
eval "$(cargo run --quiet --bin keygen)"
PK_B64="${PUBLIC_KEY:?}"
SK_B64="${SECRET_KEY:?}"
echo "  OK"

DATA_B64="$(echo -n "Integration test payload" | base64 | tr -d '\n')"

ZK_ENABLED=false
if [ -f "build/circuits/data_commitment_final.zkey" ] && [ -f "build/circuits/data_commitment_verification_key.json" ]; then
  ZK_ENABLED=true
fi
PY_GEN_PROOF=False
if [ "$ZK_ENABLED" = true ]; then
  PY_GEN_PROOF=True
fi

echo "[3/6] Wrapping data..."
WRAP_JSON="$(python3 - <<PY
import json
print(json.dumps({
  "data": "${DATA_B64}",
  "recipients": ["${PK_B64}"],
  "generate_proof": ${PY_GEN_PROOF},
  "circuit": "data_commitment",
}))
PY
)"

WRAP_RESP="$(curl -sf -X POST "$BASE_URL/api/v1/wrap" -H "Content-Type: application/json" -d "$WRAP_JSON")"
PACKAGE="$(python3 -c 'import json,sys; print(json.load(sys.stdin)["package"])' <<<"$WRAP_RESP")"
HASH="$(python3 -c 'import json,sys; print(json.load(sys.stdin)["package_hash"])' <<<"$WRAP_RESP")"
echo "  Package hash: $HASH"

if [ "$ZK_ENABLED" = true ]; then
  echo "[4/6] Fetching verification key..."
  VK_RESP="$(curl -sf "$BASE_URL/api/v1/zk/vk/data_commitment")"
  VK_HASH="$(python3 -c 'import json,sys; print(json.load(sys.stdin)["verification_key_hash"])' <<<"$VK_RESP")"
  echo "  VK hash: $VK_HASH"
else
  echo "[4/6] ZK toolchain not configured; skipping VK fetch"
fi

echo "[5/6] Unwrapping data..."
UNWRAP_JSON="$(python3 - <<PY
import json
print(json.dumps({
  "package": "${PACKAGE}",
  "recipient_public_key": "${PK_B64}",
  "recipient_secret_key": "${SK_B64}",
}))
PY
)"

UNWRAP_RESP="$(curl -sf -X POST "$BASE_URL/api/v1/unwrap" -H "Content-Type: application/json" -d "$UNWRAP_JSON")"
RECOVERED_B64="$(python3 -c 'import json,sys; print(json.load(sys.stdin)["data"])' <<<"$UNWRAP_RESP")"
RECOVERED="$(echo "$RECOVERED_B64" | base64 -d)"
echo "  Recovered: $RECOVERED"

echo "[6/6] Verifying..."
if [ "$RECOVERED" = "Integration test payload" ]; then
  echo "=== INTEGRATION TEST PASSED ==="
  exit 0
else
  echo "=== INTEGRATION TEST FAILED ==="
  exit 1
fi
