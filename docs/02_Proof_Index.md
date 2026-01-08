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
| `TaskCT.possible_seqPow_succ` | MultiRound.lean | 61 | Serial multi-round possibility |
| `TaskCT.possible_parPow_succ` | MultiRound.lean | 75 | Parallel multi-round possibility |

## BB84 Multi-Round

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `bb84_attackSeqPow_impossible` | BB84/MultiRound.lean | 34 | Reduction for serial repetition |
| `bb84_attackParPow_impossible` | BB84/MultiRound.lean | 40 | Reduction for parallel repetition |

## Concrete Witnesses

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `triangle_no_global` | EmpiricalModel.lean | 281 | Triangle has no global section |
| `not_implements_copyUnion` | QubitLike.lean | 152 | QubitLike cannot clone union |
| `qubitLikeSuperinfo` | QubitLike.lean | 234 | Concrete superinfo medium |
| `bb84Superinfo` | BB84/Superinfo.lean | 70 | BB84 superinformation medium |
| `copyAll_impossible` | BB84/Constructors.lean | 161 | No-cloning witness for BB84 |
| `bb84_secure` | BB84/Security.lean | 22 | BB84 secure against eavesdropping |
| `intercept_resend_impossible` | BB84/Security.lean | 26 | Canonical attack is CT-impossible |
| `expectedQBER_eq_rate_div_4` | BB84/ErrorRate/InterceptResend.lean | 35 | Intercept-resend yields QBER = p/4 |
| `full_interception_detected` | BB84/ErrorRate/Threshold.lean | 33 | 25% > 11% threshold |

## E91 (Toy, CT‑Native)

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `copyAll_impossible` | E91/Constructors.lean | 119 | No universal cloning (toy) |
| `e91_secure` | E91/Security.lean | 24 | E91 secure against eavesdropping |
| `intercept_impossible` | E91/Security.lean | 27 | Canonical intercept strategy impossible |

## Physical Modality

| Theorem | File | Line | Description |
|---------|------|------|-------------|
| `PhysicalModality.not_toFun_of_not` | PhysicalModality.lean | 47 | Core polarity lemma |
| `PropCT.toPhysicalModality` | TaskPossible.lean | 67 | PropCT induces modality |
| `TaskSpec.toPhysicalModality` | TaskSpec.lean | 42 | TaskSpec induces modality |
