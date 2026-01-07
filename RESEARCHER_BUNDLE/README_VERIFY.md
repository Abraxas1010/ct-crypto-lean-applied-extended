# CT Crypto: One-Command Verification

## Quick Start

```bash
./scripts/verify_ct_crypto.sh
```

This script will:
1. Check your Lean toolchain
2. Verify zero sorry/admit in codebase
3. Build the library with `--wfail`
4. Verify key theorems exist
5. Print axiom footprint

## Prerequisites

- Lean 4.24.0 (or compatible)
- `lake` build tool
- Git (for Mathlib dependency)

## Manual Build

```bash
# Get dependencies
lake update

# Build
lake build

# Check specific theorem
lake env lean -c 'import HeytingLean; #check superinfo_secure_against_eavesdropping'
```

## Key Files

| File | Content |
|------|---------|
| `HeytingLean/Crypto/ConstructiveHardnessCore.lean` | Umbrella import |
| `HeytingLean/Crypto/ConstructiveHardness/Security.lean` | Main security theorem |
| `HeytingLean/Constructor/CT/Examples/QubitLike.lean` | Concrete superinfo witness |

## Expected Output

```
==============================================
 CT Crypto Verification Script
==============================================

[1/5] Checking Lean toolchain...
  Lean version: Lean (version 4.24.0, ...)

[2/5] Checking for sorry/admit...
  OK: Zero sorry/admit found

[3/5] Building library (strict mode)...
  OK: Library build passed

[4/5] Verifying key theorems...
  OK: HeytingLean.Crypto.ConstructiveHardness.PhysicalModality
  OK: HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
  ...

[5/5] Checking axiom footprint...
  'superinfo_secure_against_eavesdropping' depends on axioms: [propext, ...]

==============================================
 VERIFICATION PASSED
==============================================
```
