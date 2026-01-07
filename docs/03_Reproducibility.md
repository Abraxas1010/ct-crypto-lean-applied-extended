# CT Crypto: Reproducibility Guide

## Quick Verification

```bash
cd RESEARCHER_BUNDLE
./scripts/verify_ct_crypto.sh
```

## Manual Build Steps

### 1. Prerequisites

- Lean 4.24.0 or compatible
- `elan` (Lean version manager)
- Git

### 2. Install Lean

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.elan/env
```

### 3. Build

```bash
cd RESEARCHER_BUNDLE
lake update
lake build
```

### 4. Verify Key Theorems

```bash
lake env lean -c '
import HeytingLean
#check HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
#check HeytingLean.Crypto.ConstructiveHardness.composed_security
#check HeytingLean.Constructor.CT.Examples.qubitLikeSuperinfo
#check HeytingLean.LoF.CryptoSheaf.Quantum.triangle_no_global
'
```

### 5. Check Axioms

```bash
lake env lean -c '
import HeytingLean
#print axioms HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
#print axioms HeytingLean.Crypto.ConstructiveHardness.composed_security
'
```

## Expected Results

- Zero `sorry` / `admit`
- Clean `lake build` with `--wfail`
- All theorems type-check
- `composed_security` uses no axioms (constructive!)

## Troubleshooting

### "lake: command not found"

Run `source ~/.elan/env` or add elan to your PATH.

### "could not find Mathlib"

Run `lake update` to fetch dependencies.

### Build fails with timeout

Increase timeout: `lake build --jobs 4`
