#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "[ct-wrap] sanity checks"

if command -v cargo >/dev/null 2>&1; then
  echo "[ct-wrap] cargo test"
  cargo test
else
  echo "[ct-wrap] NOTE: cargo not found; skipping Rust compilation/tests"
fi

if command -v node >/dev/null 2>&1; then
  echo "[ct-wrap] node present"
else
  echo "[ct-wrap] NOTE: node not found; skipping ZK script checks"
fi

echo "[ct-wrap] done"

