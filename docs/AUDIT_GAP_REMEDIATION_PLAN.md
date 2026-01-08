# CT-Crypto Audit Gap Remediation Plan

**Purpose:** Step-by-step instructions for an agent to address the outstanding audit gaps identified in the expert review of the CT-Crypto formalization.

**Date:** 2026-01-08
**Priority Order:** P0 (critical) → P1 (important) → P2 (enhancement)

---

## Overview of Gaps

| Gap | Description | Priority | Effort |
|-----|-------------|----------|--------|
| **A** | Security theorem is conditional; "requires cloning" lemmas are tautological | P0 | Medium |
| **B** | TaskCT is an interface, not full CT formalization | P1 | Medium |
| **E** | DI claims are Bell foundations only, not full DI-QKD security | P2 | High |

---

## Gap A (P0): Non-Tautological Security Proof

### Problem Statement

Current state:
- `superinfo_secure_against_eavesdropping` requires hypothesis `hRequiresCloning : CT.possible E.intercept → CT.possible M.copyXY`
- BB84/E91 lemmas define `eveInterceptTask := copyAll`, making "requires cloning" trivially true
- This proves security only against intercept-resend attacks, not all eavesdropping

Goal: Prove that ANY information-gaining attack on BB84/E91 necessarily implies cloning capability.

### Research Summary

The **information-disturbance tradeoff** is a well-established quantum result:
- "Every measurement that extracts information about a general quantum system necessarily causes an unavoidable disturbance" ([Universality in Information-Disturbance Tradeoff](https://link.springer.com/article/10.1007/s00023-018-0724-0))
- Optimal cloning attacks cause QBER of ~14.6% for BB84; security threshold is 11% ([High-dimensional cloning](https://www.science.org/doi/10.1126/sciadv.1601915))
- The phase-covariant cloning machine is optimal for BB84-type states ([Quantum cloning machines](https://iop.cas.cn/xwzx/kydt/201411/P020141128601608571942.pdf))

### Implementation Strategy

**Approach: Formalize the Optimal Cloning Bound**

The key insight is that for BB84:
1. Eve's best strategy is optimal cloning (phase-covariant cloner)
2. Optimal cloning has a known fidelity bound: F = (1 + 1/√2)/2 ≈ 0.854
3. Any fidelity above this requires the original (i.e., perfect cloning)
4. Therefore: Eve gains information I(E;K) > 0 ⟹ Eve performs (at least) approximate cloning

### Step-by-Step Instructions

#### Step A1: Define Cloning Fidelity

**File:** `HeytingLean/Crypto/QKD/BB84/CloningFidelity.lean`

```lean
/-!
# Optimal Cloning Fidelity Bounds

The optimal universal cloning fidelity for qubits is F = 5/6.
The optimal phase-covariant (BB84-relevant) fidelity is F = (1 + 1/√2)/2.
-/

/-- Fidelity of a cloning operation. -/
def CloningFidelity (ρ_original ρ_clone : DensityMatrix n) : ℝ :=
  -- trace(√(√ρ_original · ρ_clone · √ρ_original))²
  sorry -- Use Mathlib's trace and matrix sqrt

/-- The optimal phase-covariant cloning fidelity for qubits. -/
def optimalPCFidelity : ℝ := (1 + 1 / Real.sqrt 2) / 2

theorem optimalPCFidelity_bound : optimalPCFidelity < 1 := by
  unfold optimalPCFidelity
  -- 0.854 < 1
  sorry
```

#### Step A2: Define Information Gain

**File:** `HeytingLean/Crypto/QKD/BB84/InformationGain.lean`

```lean
/-!
# Eve's Information Gain

Formalize the mutual information I(E;K) that Eve obtains about the key.
-/

/-- Eve's information gain from an attack strategy. -/
structure EveInformationGain where
  /-- Mutual information between Eve's system and the key. -/
  mutualInfo : ℝ
  /-- Non-negativity. -/
  nonneg : 0 ≤ mutualInfo

/-- An attack is information-gaining if Eve learns something about the key. -/
def InformationGaining (E : EavesdroppingStrategy σ CT) (gain : EveInformationGain) : Prop :=
  gain.mutualInfo > 0
```

#### Step A3: Prove Information-Disturbance Tradeoff

**File:** `HeytingLean/Crypto/QKD/BB84/InfoDisturbance.lean`

```lean
/-!
# Information-Disturbance Tradeoff for BB84

Key theorem: Any information-gaining attack on BB84 requires approximate cloning,
and approximate cloning is bounded by the optimal cloning fidelity.
-/

/-- The QBER (Quantum Bit Error Rate) induced by an attack. -/
def attackQBER (E : EavesdroppingStrategy BB84Substrate bb84TaskCT) : ℝ := sorry

/-- Optimal cloning attack induces QBER of approximately 14.6%. -/
def optimalCloningQBER : ℝ := 0.146

/-- BB84 security threshold: QBER must be below 11% for secure key distillation. -/
def bb84SecurityThreshold : ℝ := 0.11

/-- KEY THEOREM: If Eve gains information, she induces detectable disturbance.
    Specifically: I(E;K) > 0 ⟹ QBER > 0 -/
theorem info_gain_implies_disturbance
    (E : EavesdroppingStrategy BB84Substrate bb84TaskCT)
    (gain : EveInformationGain)
    (h_gains : InformationGaining E gain) :
    attackQBER E > 0 := by
  sorry -- This is the core information-disturbance tradeoff

/-- Corollary: If QBER = 0 (no disturbance), Eve gains no information. -/
theorem no_disturbance_no_information
    (E : EavesdroppingStrategy BB84Substrate bb84TaskCT)
    (h_no_qber : attackQBER E = 0) :
    ∀ gain : EveInformationGain, ¬InformationGaining E gain := by
  intro gain h_gains
  have h := info_gain_implies_disturbance E gain h_gains
  linarith
```

#### Step A4: Connect to Cloning Requirement

**File:** `HeytingLean/Crypto/QKD/BB84/SecurityStrengthened.lean`

```lean
/-!
# Strengthened BB84 Security

Connect information-disturbance to the cloning requirement.
-/

/-- An attack that gains information must perform approximate cloning. -/
theorem info_gaining_requires_cloning
    (E : EavesdroppingStrategy BB84Substrate bb84TaskCT)
    (gain : EveInformationGain)
    (h_gains : InformationGaining E gain) :
    ∃ (approxClone : CTask BB84Substrate),
      bb84TaskCT.possible approxClone ∧
      CloningFidelity_ge approxClone (1 - attackQBER E) := by
  sorry

/-- Approximate cloning with fidelity > optimalPCFidelity requires perfect cloning. -/
theorem high_fidelity_requires_perfect_clone
    (clone : CTask BB84Substrate)
    (h_fidelity : CloningFidelity clone > optimalPCFidelity) :
    bb84TaskCT.possible clone → bb84TaskCT.possible copyAll := by
  sorry

/-- MAIN THEOREM: Any information-gaining attack implies cloning capability.
    This makes the security theorem non-tautological. -/
theorem any_info_attack_requires_cloning
    (E : EavesdroppingStrategy BB84Substrate bb84TaskCT)
    (h_info : ∃ gain, InformationGaining E gain) :
    bb84TaskCT.possible E.intercept → bb84TaskCT.possible bb84Superinfo.copyXY := by
  sorry
```

#### Step A5: Update Security Theorem

**File:** `HeytingLean/Crypto/QKD/BB84/Security.lean` (update existing)

Add new theorem:

```lean
/-- Strengthened BB84 security: secure against ALL information-gaining attacks. -/
theorem bb84_secure_against_all_info_attacks :
    ∀ (E : EavesdroppingStrategy BB84Substrate bb84TaskCT),
      (∃ gain, InformationGaining E gain) →
      bb84TaskCT.impossible E.intercept := by
  intro E h_info
  apply bb84_secure E
  exact any_info_attack_requires_cloning E h_info
```

### Verification Checklist for Gap A

- [ ] `CloningFidelity.lean` compiles with `lake build --wfail`
- [ ] `InformationGain.lean` compiles
- [ ] `InfoDisturbance.lean` compiles (may have `sorry` initially)
- [ ] `SecurityStrengthened.lean` compiles
- [ ] `bb84_secure_against_all_info_attacks` type-checks
- [ ] Run `./scripts/guard_no_sorry.sh` (will fail initially; track sorries)
- [ ] Document remaining sorries as explicit axioms if physics-dependent

---

## Gap B (P1): Complete CT Formalization

### Problem Statement

Current `TaskCT` provides:
- Constructor types with `implements`
- Serial/parallel composition with soundness

Missing (per Deutsch-Marletto):
- Identity constructors
- Associativity/commutativity of composition
- Interoperability principle (Principle III)
- Distinguishability principles (Principles IV, V)

### Research Summary

From [Constructor Theory of Information](https://pmc.ncbi.nlm.nih.gov/articles/PMC4309123/):

**Principle I:** All laws expressible as possible/impossible transformations
**Principle II:** Locality - state of S₁⊕S₂ is pair (x,y)
**Principle III:** Interoperability - S₁×S₂ is information variable if S₁, S₂ are
**Principle IV:** Pairwise distinguishability extends to full distinguishability
**Principle V:** Distinguishability from attribute extends to distinguishability

**Composition Laws:**
- Parallel: A⊗B performs A on M and B on N simultaneously
- Serial: BA when Out(A)=In(B), performs A then B

### Step-by-Step Instructions

#### Step B1: Add Identity Constructor

**File:** `HeytingLean/Constructor/CT/TaskExistence.lean` (extend)

```lean
/-- Extended TaskCT with identity and algebraic laws. -/
structure TaskCTFull (σ : Type u) extends TaskCT σ where
  /-- Identity constructor (does nothing). -/
  idCtor : Ctor
  /-- Identity implements the identity task. -/
  implements_id : implements idCtor Task.id

  /-- Serial composition is associative. -/
  seq_assoc : ∀ c₁ c₂ c₃, seqCtor (seqCtor c₁ c₂) c₃ = seqCtor c₁ (seqCtor c₂ c₃)
  /-- Identity is left unit for serial composition. -/
  seq_id_left : ∀ c, seqCtor idCtor c = c
  /-- Identity is right unit for serial composition. -/
  seq_id_right : ∀ c, seqCtor c idCtor = c

  /-- Parallel composition is associative. -/
  par_assoc : ∀ c₁ c₂ c₃, parCtor (parCtor c₁ c₂) c₃ = parCtor c₁ (parCtor c₂ c₃)
  /-- Parallel composition is commutative (up to substrate reordering). -/
  par_comm : ∀ c₁ c₂, parCtor c₁ c₂ = parCtor c₂ c₁  -- May need braiding
```

#### Step B2: Formalize Interoperability Principle

**File:** `HeytingLean/Constructor/CT/Interoperability.lean` (new)

```lean
/-!
# Interoperability Principle (Constructor Theory Principle III)

If S₁ and S₂ are information variables, then S₁ × S₂ is an information variable.
-/

namespace HeytingLean.Constructor.CT

/-- Interoperability: product of information variables is an information variable. -/
class Interoperability (σ₁ σ₂ : Type*) (CT₁ : TaskCT σ₁) (CT₂ : TaskCT σ₂)
    (CT_prod : TaskCT (σ₁ × σ₂)) where
  /-- If X is info variable on σ₁ and Y is info variable on σ₂,
      then X × Y is info variable on σ₁ × σ₂. -/
  product_info :
    ∀ (X : InfoVariable σ₁ CT₁) (Y : InfoVariable σ₂ CT₂),
      InfoVariable (σ₁ × σ₂) CT_prod

end HeytingLean.Constructor.CT
```

#### Step B3: Formalize Distinguishability Principles

**File:** `HeytingLean/Constructor/CT/Distinguishability.lean` (new)

```lean
/-!
# Distinguishability Principles (Constructor Theory Principles IV and V)
-/

namespace HeytingLean.Constructor.CT

variable {σ : Type*} (CT : TaskCT σ)

/-- Two attributes are distinguishable if there exists a task that
    maps them to distinct, preparable output states. -/
def Distinguishable (x y : σ) : Prop :=
  ∃ (T : Task σ) (out_x out_y : σ),
    CT.possible T ∧
    out_x ≠ out_y ∧
    T.maps x out_x ∧
    T.maps y out_y

/-- A variable (set of attributes) is distinguishable if any pair is distinguishable. -/
def VariableDistinguishable (S : Set σ) : Prop :=
  ∀ x y : σ, x ∈ S → y ∈ S → x ≠ y → Distinguishable CT x y

/-- Principle IV: Pairwise distinguishability implies full distinguishability. -/
class PrincipleIV where
  pairwise_implies_full :
    ∀ (S : Finset σ),
      (∀ x y : σ, x ∈ S → y ∈ S → x ≠ y → Distinguishable CT x y) →
      VariableDistinguishable CT S

/-- Principle V: Distinguishability from an attribute extends. -/
class PrincipleV where
  extend_distinguishability :
    ∀ (x : σ) (Y : Set σ),
      (∀ y ∈ Y, Distinguishable CT x y) →
      ∀ y ∈ Y, Distinguishable CT y x

end HeytingLean.Constructor.CT
```

#### Step B4: Formalize Locality Principle

**File:** `HeytingLean/Constructor/CT/Locality.lean` (new)

```lean
/-!
# Locality Principle (Constructor Theory Principle II)

The state of S₁ ⊕ S₂ is the pair (x, y), and constructions on S₁ alone
cannot affect the state of S₂.
-/

namespace HeytingLean.Constructor.CT

/-- Locality: a task on the first component doesn't affect the second. -/
class Locality (σ₁ σ₂ : Type*) (CT : TaskCT (σ₁ × σ₂)) where
  /-- Lifting a task on σ₁ to σ₁ × σ₂. -/
  liftLeft : Task σ₁ → Task (σ₁ × σ₂)
  /-- Lifted task preserves the second component. -/
  lift_preserves_right :
    ∀ (T : Task σ₁) (x : σ₁) (y : σ₂) (x' : σ₁),
      (liftLeft T).maps (x, y) (x', y)

end HeytingLean.Constructor.CT
```

### Verification Checklist for Gap B

- [ ] `TaskCTFull` structure compiles
- [ ] `Interoperability.lean` compiles
- [ ] `Distinguishability.lean` compiles
- [ ] `Locality.lean` compiles
- [ ] Update `bb84TaskCT` to be instance of `TaskCTFull` (if possible)
- [ ] Run full build: `lake build --wfail`

---

## Gap E (P2): DI-QKD Entropy Bounds

### Problem Statement

Current state:
- CHSH inequality proven: |S| ≤ 2 for LHV
- Tsirelson bound proven: |S| ≤ 2√2 for quantum
- `chsh_violation_no_lhv` proven

Missing:
- Min-entropy from CHSH violation
- Entropy Accumulation Theorem
- Finite-key security bounds

### Research Summary

From [Entropy Accumulation Theorem](https://www.nature.com/articles/s41467-017-02307-4):
- EAT relates total entropy to per-round entropy
- Key result: H_min(K|E) ≥ n·h(S) - O(√n) where h(S) is entropy rate from CHSH value S

From [Lean-QuantumInfo Library](https://github.com/Timeroot/Lean-QuantumInfo):
- 1000+ theorems on quantum information in Lean 4
- Includes CPTP maps, entropy definitions, Quantum Stein's Lemma
- Potential dependency or reference for our work

### Step-by-Step Instructions

#### Step E1: Add Lean-QuantumInfo as Dependency (Optional)

**File:** `lakefile.lean` (update)

```lean
-- Consider adding Lean-QuantumInfo for entropy definitions
-- require quantumInfo from git "https://github.com/Timeroot/Lean-QuantumInfo"
```

Note: May require compatibility work with Mathlib version.

#### Step E2: Define Min-Entropy

**File:** `HeytingLean/Crypto/QKD/E91/DI/Entropy/MinEntropy.lean` (new)

```lean
/-!
# Min-Entropy Definitions

Conditional min-entropy H_min(A|B) bounds Eve's guessing probability.
-/

namespace HeytingLean.Crypto.QKD.E91.DI.Entropy

/-- Conditional min-entropy (simplified definition). -/
def condMinEntropy (ρ_AB : DensityMatrix (n × m)) : ℝ :=
  -Real.log (guessingProbability ρ_AB)

/-- Guessing probability: max probability Eve guesses A given B. -/
def guessingProbability (ρ_AB : DensityMatrix (n × m)) : ℝ := sorry

/-- Min-entropy is non-negative for normalized states. -/
theorem condMinEntropy_nonneg (ρ : DensityMatrix (n × m)) (h : normalized ρ) :
    0 ≤ condMinEntropy ρ := by
  sorry

end HeytingLean.Crypto.QKD.E91.DI.Entropy
```

#### Step E3: CHSH-to-Entropy Bound

**File:** `HeytingLean/Crypto/QKD/E91/DI/Entropy/CHSHEntropy.lean` (new)

```lean
/-!
# Min-Entropy from CHSH Violation

The key result connecting Bell inequality violation to cryptographic security:
Higher CHSH violation ⟹ more min-entropy ⟹ Eve knows less.
-/

namespace HeytingLean.Crypto.QKD.E91.DI.Entropy

/-- The entropy rate function h(S) for CHSH value S.
    For S = 2√2 (Tsirelson): h(S) = 1 bit
    For S = 2 (classical): h(S) = 0 bits -/
def entropyRateFromCHSH (S : ℝ) : ℝ :=
  if S ≤ 2 then 0
  else 1 - Real.log (1 + Real.sqrt (1 - ((S - 2) / (2 * Real.sqrt 2 - 2))^2)) / Real.log 2

/-- KEY THEOREM: CHSH violation bounds min-entropy.
    If observed CHSH value is S > 2, then H_min(K|E) ≥ h(S) per round. -/
theorem chsh_violation_bounds_entropy
    (S : ℝ) (h_violation : S > 2) (h_tsirelson : S ≤ 2 * Real.sqrt 2) :
    entropyRateFromCHSH S > 0 := by
  sorry

/-- At Tsirelson bound, Eve has zero information. -/
theorem tsirelson_maximal_entropy :
    entropyRateFromCHSH (2 * Real.sqrt 2) = 1 := by
  sorry

end HeytingLean.Crypto.QKD.E91.DI.Entropy
```

#### Step E4: Entropy Accumulation (Interface)

**File:** `HeytingLean/Crypto/QKD/E91/DI/Entropy/Accumulation.lean` (new)

```lean
/-!
# Entropy Accumulation Theorem (Interface)

The EAT states that total min-entropy over n rounds is approximately n times
the per-round entropy, with finite-size corrections.

This is an INTERFACE - the full proof is highly technical and marked as future work.
-/

namespace HeytingLean.Crypto.QKD.E91.DI.Entropy

/-- Protocol parameters for n-round DI-QKD. -/
structure DIQKDParams where
  /-- Number of rounds. -/
  n : ℕ
  /-- Observed CHSH value (averaged). -/
  observedCHSH : ℝ
  /-- Security parameter ε. -/
  epsilon : ℝ
  /-- CHSH > 2. -/
  h_violation : observedCHSH > 2
  /-- ε > 0. -/
  h_eps_pos : epsilon > 0

/-- ENTROPY ACCUMULATION THEOREM (axiomatized interface).

    For an n-round DI protocol with observed CHSH value S:
    H_min(K|E) ≥ n · h(S) - O(√n · log(1/ε))

    This is the main technical tool for DI-QKD security. -/
axiom entropy_accumulation_theorem (params : DIQKDParams) :
    ∃ (H_min_total : ℝ),
      H_min_total ≥ params.n * entropyRateFromCHSH params.observedCHSH -
                    Real.sqrt params.n * Real.log (1 / params.epsilon)

end HeytingLean.Crypto.QKD.E91.DI.Entropy
```

#### Step E5: DI-QKD Security Statement

**File:** `HeytingLean/Crypto/QKD/E91/DI/Security/FullSecurity.lean` (new)

```lean
/-!
# Full DI-QKD Security (Interface)

Combining entropy accumulation with privacy amplification gives the
full security statement for device-independent QKD.
-/

namespace HeytingLean.Crypto.QKD.E91.DI.Security

open HeytingLean.Crypto.QKD.E91.DI.Entropy

/-- Secure key length for DI-QKD. -/
def secureKeyLength (params : DIQKDParams) : ℝ :=
  params.n * entropyRateFromCHSH params.observedCHSH -
  Real.sqrt params.n * Real.log (1 / params.epsilon) -
  params.n * leakage  -- Error correction leakage
where
  leakage : ℝ := 0.1  -- Placeholder

/-- DI-QKD SECURITY THEOREM (interface).

    If the observed CHSH value exceeds 2, and the protocol completes,
    then Alice and Bob share a key that is ε-secure against any adversary
    (including one controlling the devices). -/
axiom di_qkd_security (params : DIQKDParams) :
    secureKeyLength params > 0 →
    ∃ (key_length : ℕ),
      key_length = ⌊secureKeyLength params⌋ ∧
      SecureKey params.epsilon key_length

/-- A key is ε-secure if Eve's information is bounded. -/
def SecureKey (epsilon : ℝ) (length : ℕ) : Prop :=
  ∀ (eve_info : ℝ), eve_info ≤ epsilon

end HeytingLean.Crypto.QKD.E91.DI.Security
```

### Verification Checklist for Gap E

- [ ] `MinEntropy.lean` compiles
- [ ] `CHSHEntropy.lean` compiles
- [ ] `Accumulation.lean` compiles (with axiom)
- [ ] `FullSecurity.lean` compiles (with axiom)
- [ ] Document axioms clearly in TECHNICAL_CLAIMS
- [ ] Run full build: `lake build --wfail`

---

## Execution Order

### Phase 1: Gap A (P0) - 3-5 days

1. Create `CloningFidelity.lean`
2. Create `InformationGain.lean`
3. Create `InfoDisturbance.lean`
4. Create `SecurityStrengthened.lean`
5. Update `Security.lean` with new theorem
6. Run verification, track sorries

### Phase 2: Gap B (P1) - 2-3 days

1. Extend `TaskExistence.lean` with `TaskCTFull`
2. Create `Interoperability.lean`
3. Create `Distinguishability.lean`
4. Create `Locality.lean`
5. Update instances to use extended structure

### Phase 3: Gap E (P2) - 3-5 days

1. Create `MinEntropy.lean`
2. Create `CHSHEntropy.lean`
3. Create `Accumulation.lean` (axiom-based)
4. Create `FullSecurity.lean` (axiom-based)
5. Update TECHNICAL_CLAIMS with new scope

### Phase 4: Documentation Update - 1 day

1. Update `TECHNICAL_CLAIMS_FOR_REVIEW.md`
2. Re-run `#print axioms` for all new theorems
3. Update "What is NOT claimed" section
4. Create summary of new capabilities

---

## References

### Gap A (Information-Disturbance)
- [Universality in Information-Disturbance Tradeoff](https://link.springer.com/article/10.1007/s00023-018-0724-0)
- [Measurement-Disturbance Outperforming Optimal Cloning](https://arxiv.org/abs/1808.07882)
- [High-dimensional Cloning Applications](https://www.science.org/doi/10.1126/sciadv.1601915)

### Gap B (Constructor Theory)
- [Constructor Theory (Deutsch 2013)](https://arxiv.org/abs/1210.7439)
- [Constructor Theory of Information](https://pmc.ncbi.nlm.nih.gov/articles/PMC4309123/)
- [Constructor Theory of Time (2025)](https://arxiv.org/abs/2505.08692)

### Gap E (DI-QKD)
- [Practical DI-QKD via Entropy Accumulation](https://www.nature.com/articles/s41467-017-02307-4)
- [Security from Generalised Entropy Accumulation](https://www.nature.com/articles/s41467-023-40920-8)
- [Lean-QuantumInfo Library](https://github.com/Timeroot/Lean-QuantumInfo)
- [Quantum Stein's Lemma Formalization](https://arxiv.org/abs/2510.08672)

---

## Success Criteria

After completing all phases:

1. **Gap A resolved:** `bb84_secure_against_all_info_attacks` compiles (possibly with physics axioms)
2. **Gap B resolved:** `TaskCTFull` with Principles II-V as typeclasses
3. **Gap E resolved:** `di_qkd_security` statement with explicit axiom marking
4. **Documentation updated:** TECHNICAL_CLAIMS reflects new capabilities and remaining axioms
5. **Build passes:** `lake build --wfail` succeeds
6. **Sorry-free or documented:** All sorries either eliminated or converted to explicit axioms with justification

---

*Generated: 2026-01-08*
*For use by Lean 4 QA Agent*
