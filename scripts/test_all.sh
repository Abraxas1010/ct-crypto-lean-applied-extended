#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "=== CT-Crypto Full Test Suite ==="

echo ""
echo "[1/2] Lean verification..."
cd "$ROOT/RESEARCHER_BUNDLE"
./scripts/verify_ct_crypto.sh

echo ""
echo "[2/2] Rust tests..."
cd "$ROOT/ct-wrap"
# shellcheck disable=SC1091
source "${HOME}/.cargo/env" 2>/dev/null || true
cargo test

echo ""
echo "=== ALL TESTS PASSED ==="

