# CT Crypto: Dependencies

## Lean Toolchain

```
leanprover/lean4:v4.24.0
```

## Mathlib

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"
```

## Mathlib Imports Used

| Import | Purpose |
|--------|---------|
| `Mathlib.Logic.Basic` | Basic logic |
| `Mathlib.Data.Set.Basic` | Set operations |
| `Mathlib.Data.Finset.Basic` | Finite sets |
| `Mathlib.Data.Fin.Basic` | Fin types |
| `Mathlib.Data.Fintype.Prod` | `Fintype (α × β)` (BB84 state space) |
| `Mathlib.Order.CompleteLattice.Basic` | Complete lattices |
| `Mathlib.Order.Nucleus` | Nucleus (for meta-theory only) |
| `Mathlib.Data.Multiset.Basic` | Multisets |
| `Mathlib.Data.List.Basic` | Lists |
| `Mathlib.Data.Nat.Basic` | Natural numbers |
| `Mathlib.Tactic` | Tactics |

## No Custom Axioms

The formalization introduces no project-specific axioms. All theorems rely only on standard Lean kernel axioms:

- `propext` (propositional extensionality)
- `Classical.choice` (axiom of choice, from Set layer)
- `Quot.sound` (quotient soundness)

The key composition lemma `composed_security` is **completely axiom-free**.
