#!/usr/bin/env bash
# Constructor-Theoretic Cryptography - One-Command Verification
# Usage: ./scripts/verify_ct_crypto.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUNDLE_DIR="$(dirname "$SCRIPT_DIR")"

cd "$BUNDLE_DIR"

echo "=============================================="
echo " CT Crypto Verification Script"
echo "=============================================="
echo ""

# 1. Check toolchain
echo "[1/5] Checking Lean toolchain..."
if ! command -v lake &> /dev/null; then
    echo "ERROR: lake not found. Please install Lean 4."
    exit 1
fi
LEAN_VERSION=$(lake env lean --version 2>/dev/null | head -n1 || echo "unknown")
echo "  Lean version: $LEAN_VERSION"

# 2. Guard: no sorry/admit
echo ""
echo "[2/5] Checking for sorry/admit..."
SORRY_COUNT=$(grep -r --include="*.lean" -E '\bsorry\b|\badmit\b' HeytingLean/ 2>/dev/null | grep -v "-- sorry" | wc -l || true)
if [ "$SORRY_COUNT" -gt 0 ]; then
    echo "ERROR: Found $SORRY_COUNT sorry/admit occurrences!"
    grep -r --include="*.lean" -E '\bsorry\b|\badmit\b' HeytingLean/ | head -20
    exit 1
fi
echo "  OK: Zero sorry/admit found"

# 3. Build library
echo ""
echo "[3/5] Building library (strict mode)..."
lake build --wfail 2>&1 | tee reports/build_log.txt
echo "  OK: Library build passed"

# 4. Verify key theorems exist
echo ""
echo "[4/5] Verifying key theorems..."

verify_theorem() {
    local THEOREM=$1
    if lake env lean -c "import HeytingLean; #check $THEOREM" 2>/dev/null; then
        echo "  OK: $THEOREM"
    else
        echo "  FAIL: $THEOREM not found"
        return 1
    fi
}

verify_theorem "HeytingLean.Crypto.ConstructiveHardness.PhysicalModality"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.contextuality_implies_physImpossible"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.triangle_physImpossible"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.composed_security"
verify_theorem "HeytingLean.Constructor.CT.Examples.qubitLikeSuperinfo"
verify_theorem "HeytingLean.LoF.CryptoSheaf.Quantum.triangle_no_global"

# 5. Axiom footprint
echo ""
echo "[5/5] Checking axiom footprint..."
lake env lean -c "
import HeytingLean

#print axioms HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
#print axioms HeytingLean.Crypto.ConstructiveHardness.composed_security
" 2>&1 | tee reports/axioms.txt

echo ""
echo "=============================================="
echo " VERIFICATION PASSED"
echo "=============================================="
echo ""
echo "Key results verified:"
echo "  - PhysicalModality: sound (Phi P -> P)"
echo "  - contextuality_implies_physImpossible: KS -> physical impossibility"
echo "  - triangle_physImpossible: concrete witness"
echo "  - superinfo_secure_against_eavesdropping: main security theorem"
echo "  - composed_security: composition transfer"
echo "  - qubitLikeSuperinfo: concrete superinfo example"
echo ""
echo "Build log: reports/build_log.txt"
echo "Axioms: reports/axioms.txt"
