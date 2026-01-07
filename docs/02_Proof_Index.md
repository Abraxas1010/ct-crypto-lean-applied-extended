# CT Crypto: Proof Index

## Core Security Theorems

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `superinfo_secure_against_eavesdropping` | Security.lean | 41 | Main security result |
| `composed_security` | Composition.lean | 53 | Compositional transfer (axiom-free!) |
| `impossible_seq_of_impossible` | Composition.lean | 33 | Serial decomposition |

## Contextuality Bridge

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `contextuality_implies_physImpossible` | ContextualityPhysical.lean | 41 | KS -> physical impossibility |
| `triangle_physImpossible` | ContextualityPhysical.lean | 56 | Concrete witness |
| `contextuality_implies_not_globalSectionTask` | ContextualityPhysical.lean | 31 | Core constructive step |

## Task Algebra

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `TaskCT.possible_seq` | TaskExistence.lean | 57 | Serial composition preserves possibility |
| `TaskCT.possible_par` | TaskExistence.lean | 65 | Parallel composition preserves possibility |
| `contextuality_implies_task_impossible` | TaskSpec.lean | 64 | Task-level impossibility |

## Concrete Witnesses

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `triangle_no_global` | EmpiricalModel.lean | 281 | Triangle has no global section |
| `not_implements_copyUnion` | QubitLike.lean | 152 | QubitLike cannot clone union |
| `qubitLikeSuperinfo` | QubitLike.lean | 234 | Concrete superinfo medium |

## Physical Modality

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `PhysicalModality.not_toFun_of_not` | PhysicalModality.lean | 47 | Core polarity lemma |
| `PropCT.toPhysicalModality` | TaskPossible.lean | 67 | PropCT induces modality |
| `TaskSpec.toPhysicalModality` | TaskSpec.lean | 42 | TaskSpec induces modality |
