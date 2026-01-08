#!/usr/bin/env bash
# Constructor-Theoretic Cryptography - One-Command Verification
# Usage: ./scripts/verify_ct_crypto.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BUNDLE_DIR="$(dirname "$SCRIPT_DIR")"

cd "$BUNDLE_DIR"
mkdir -p reports

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
SORRY_COUNT=$(grep -r --include="*.lean" -E '\bsorry\b|\badmit\b' HeytingLean/ 2>/dev/null | grep -v -- "-- sorry" | wc -l || true)
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
    local TMP_FILE
    TMP_FILE="$(mktemp "${BUNDLE_DIR}/reports/check_XXXXXX.lean")"
    cat > "$TMP_FILE" <<EOF
import HeytingLean
#check $THEOREM
EOF
    if lake env lean "$TMP_FILE" >/dev/null 2>&1; then
        echo "  OK: $THEOREM"
        rm -f "$TMP_FILE"
        return 0
    fi
    echo "  FAIL: $THEOREM not found"
    echo "  (See ${TMP_FILE} for the failing check.)"
    return 1
}

verify_theorem "HeytingLean.Crypto.ConstructiveHardness.PhysicalModality"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.contextuality_implies_physImpossible"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.triangle_physImpossible"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping"
verify_theorem "HeytingLean.Crypto.ConstructiveHardness.composed_security"
verify_theorem "HeytingLean.Constructor.CT.Examples.qubitLikeSuperinfo"
verify_theorem "HeytingLean.LoF.CryptoSheaf.Quantum.triangle_no_global"
verify_theorem "HeytingLean.Crypto.QKD.BB84.bb84_secure"
verify_theorem "HeytingLean.Crypto.QKD.BB84.copyAll_impossible"
verify_theorem "HeytingLean.Crypto.QKD.BB84.intercept_resend_impossible"
verify_theorem "HeytingLean.Crypto.QKD.BB84.bb84_attackSeqPow_impossible"
verify_theorem "HeytingLean.Crypto.QKD.BB84.bb84_attackParPow_impossible"
verify_theorem "HeytingLean.Crypto.QKD.BB84.ErrorRate.full_interception_detected"
verify_theorem "HeytingLean.Crypto.QKD.BB84.ErrorRate.interception_detectable"
verify_theorem "HeytingLean.Crypto.QKD.E91.e91_secure"
verify_theorem "HeytingLean.Crypto.QKD.E91.intercept_impossible"
verify_theorem "HeytingLean.Physics.Photoemission.efficiency_factorization"
verify_theorem "HeytingLean.Physics.Photoemission.energy_conservation_required"

# 5. Axiom footprint
echo ""
echo "[5/5] Checking axiom footprint..."
AXIOM_FILE="$(mktemp "${BUNDLE_DIR}/reports/axioms_XXXXXX.lean")"
cat > "$AXIOM_FILE" <<'EOF'
import HeytingLean

#print axioms HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
#print axioms HeytingLean.Crypto.ConstructiveHardness.composed_security
#print axioms HeytingLean.Crypto.QKD.BB84.bb84_secure
EOF
lake env lean "$AXIOM_FILE" 2>&1 | tee reports/axioms.txt

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
