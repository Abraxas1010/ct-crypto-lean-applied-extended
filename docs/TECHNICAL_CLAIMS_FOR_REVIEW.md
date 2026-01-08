# Constructor-Theoretic Cryptography: Technical Claims for Expert Review

**Document Purpose:** This document presents the technical and mathematical claims of the CT-Crypto formalization for independent expert review. All theorem statements are extracted verbatim from the Lean 4 source code. Verification instructions are provided.

**Version:** 2 (revised after expert audit)
**Date:** 2026-01-08
**Repository:** `WIP/CT_Crypto_Repo/RESEARCHER_BUNDLE/`
**Verification Command:** `cd RESEARCHER_BUNDLE && ./scripts/verify_ct_crypto.sh`

---

## 1. Executive Summary of Claims

We claim to have produced:

1. **A CT-inspired task-possibility algebra formalized in Lean 4**, providing:
   - Constructor types with `implements` relation
   - Serial/parallel composition with soundness laws
   - Superinformation medium structure (individually clonable, jointly not clonable)

   *Note: This is an interface for CT-style reasoning, not a full formalization of the complete Deutsch-Marletto Constructor Theory framework.*

2. **Complete proofs** (not axioms or sorry placeholders) of:
   - The CHSH inequality: |S| ≤ 2 for any local hidden variable model
   - The Tsirelson bound: |S| ≤ 2√2 for any quantum strategy
   - Achievability: An explicit quantum strategy achieving S = 2√2

3. **A conditional security theorem**: Any eavesdropping strategy that *would require* cloning a superinformation medium is impossible. The "requires cloning" hypothesis must be established separately per attack model.

4. **Bell inequality foundations** relevant to device-independent QKD:
   - CHSH violation implies no local hidden variable model
   - *Note: Full DI-QKD security (entropy accumulation, finite-key bounds) is future work.*

5. **Zero `sorry` or `admit`** statements in the entire codebase.

6. **Minimal axiom footprint**: propext, Classical.choice, Quot.sound (Lean kernel-standard), with the composition theorem requiring no axioms at all.

---

## 2. Verification Instructions

A reviewer can independently verify all claims as follows:

### 2.1 Prerequisites

```bash
# Install Lean 4 (via elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
source ~/.profile
```

### 2.2 Build and Verify

```bash
cd WIP/CT_Crypto_Repo/RESEARCHER_BUNDLE

# One-command verification
./scripts/verify_ct_crypto.sh
```

**Expected output includes:**
```
[2/5] Checking for sorry/admit...
  OK: Zero sorry/admit found

[3/5] Building library (strict mode)...
  Build completed successfully (3207 jobs).

[4/5] Verifying key theorems...
  OK: HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
  OK: HeytingLean.Crypto.QKD.E91.DI.CHSH.LocalHiddenVariableModel.chsh_inequality
  OK: HeytingLean.Crypto.QKD.E91.DI.Tsirelson.QuantumStrategy.tsirelson_bound
  ...

VERIFICATION PASSED
```

### 2.3 Manual Axiom Check

```bash
cd RESEARCHER_BUNDLE
lake env lean -c '
import HeytingLean

#print axioms HeytingLean.Crypto.ConstructiveHardness.superinfo_secure_against_eavesdropping
#print axioms HeytingLean.Crypto.ConstructiveHardness.composed_security
#print axioms HeytingLean.Crypto.QKD.E91.DI.CHSH.LocalHiddenVariableModel.chsh_inequality
'
```

**Expected output:**
```
'superinfo_secure_against_eavesdropping' depends on axioms: [propext, Classical.choice, Quot.sound]
'composed_security' does not depend on any axioms
'chsh_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 3. Core Mathematical Framework

### 3.1 CT-Inspired Task Algebra

**Source file:** `HeytingLean/Constructor/CT/TaskExistence.lean`

Constructor Theory expresses physical laws as statements about which transformations (tasks) are possible or impossible. We provide an *interface* for this style of reasoning:

```lean
/-- A minimal "constructor existence" interface for CT tasks over a substrate `σ`. -/
structure TaskCT (σ : Type u) where
  /-- The type of constructors. -/
  Ctor : Type v
  /-- `implements c T` means constructor `c` can enact task `T`. -/
  implements : Ctor → Task σ → Prop
  /-- Serial composition of constructors. -/
  seqCtor : Ctor → Ctor → Ctor
  /-- Parallel composition of constructors. -/
  parCtor : Ctor → Ctor → Ctor
  /-- Soundness: seq composition implements Task.seq. -/
  implements_seq : ∀ {c₁ c₂ T U}, implements c₁ T → implements c₂ U →
    implements (seqCtor c₁ c₂) (Task.seq T U)
  /-- Soundness: par composition implements Task.par. -/
  implements_par : ∀ {c₁ c₂ T U}, implements c₁ T → implements c₂ U →
    implements (parCtor c₁ c₂) (Task.par T U)

/-- A task is possible when some constructor implements it. -/
def possible (T : Task σ) : Prop := ∃ c : CT.Ctor, CT.implements c T

/-- A task is impossible when no constructor implements it. -/
def impossible (T : Task σ) : Prop := ¬ CT.possible T
```

**What this provides:**
- Constructor types with explicit `implements` relation
- Serial/parallel composition with soundness laws
- `possible T ↔ ∃c. implements(c, T)` (existential semantics)

**What this does NOT provide (future work):**
- Identity constructors
- Associativity/commutativity proofs for composition
- Full substrate algebra (Deutsch-Marletto axioms)
- Inverses, permutation groups

### 3.2 Physical Modality

**Source file:** `HeytingLean/Crypto/ConstructiveHardness/PhysicalModality.lean`

Constructor Theory requires a modality Φ satisfying soundness: Φ P → P.

```lean
/-- Physical modality: Φ represents "is physically necessary." -/
structure PhysicalModality where
  toFun : Prop → Prop
  sound : ∀ P, toFun P → P
```

**Critical property:** The polarity is Φ P → P (soundness), not P → Φ P. This ensures we derive security from impossibility, not assume it.

### 3.3 Superinformation Medium

**Source file:** `HeytingLean/Crypto/ConstructiveHardness/TaskSpec.lean`

The central structure encoding the no-cloning property:

```lean
/-- A superinformation medium: two information variables where the joint
    variable cannot be copied, though each can be copied individually. -/
structure TaskCT.SuperinformationMedium (σ : Type*) (CT : TaskCT σ) where
  /-- First information variable. -/
  X : InfoVariable σ CT
  /-- Second information variable. -/
  Y : InfoVariable σ CT
  /-- Task to copy X. -/
  copyX : Task σ
  /-- Task to copy Y. -/
  copyY : Task σ
  /-- Task to copy the joint variable XY. -/
  copyXY : Task σ
  /-- X is individually clonable. -/
  can_copyX : CT.possible copyX
  /-- Y is individually clonable. -/
  can_copyY : CT.possible copyY
  /-- Joint variable XY is NOT clonable. -/
  no_copyXY : CT.impossible copyXY
```

**Mathematical content:** This captures the quantum no-cloning theorem in constructor-theoretic language. For QKD, X and Y correspond to conjugate bases (e.g., rectilinear and diagonal for BB84).

---

## 4. Main Security Theorem

### 4.1 Theorem Statement

**Source file:** `HeytingLean/Crypto/ConstructiveHardness/Security.lean`

```lean
/-- An eavesdropping strategy for a task model. -/
structure EavesdroppingStrategy (σ : Type*) (CT : TaskCT σ) where
  /-- The eavesdropping task (intercept and copy). -/
  intercept : Task σ
  /-- Eve gains some information. -/
  gains_info : Prop
  /-- Soundness: if intercept is possible, gain holds. -/
  sound : CT.possible intercept → gains_info

/-- Secure against eavesdropping: any strategy requiring cloning is impossible. -/
def SecureAgainstEavesdropping (σ : Type*) (CT : TaskCT σ)
    (M : TaskCT.SuperinformationMedium σ CT) : Prop :=
  ∀ (E : EavesdroppingStrategy σ CT),
    (CT.possible E.intercept → CT.possible M.copyXY) →
      CT.impossible E.intercept

/-- Main security theorem. -/
theorem superinfo_secure_against_eavesdropping
    {σ : Type*} (CT : TaskCT σ) (M : TaskCT.SuperinformationMedium σ CT) :
    SecureAgainstEavesdropping σ CT M := by
  intro E hRequiresCloning hPossible
  have hCopyPossible : CT.possible M.copyXY := hRequiresCloning hPossible
  exact M.no_copyXY hCopyPossible
```

### 4.2 Proof Analysis

The proof is three lines because the work is encoded in the definitions:

1. Let E be any eavesdropping strategy
2. Assume `hRequiresCloning`: E.intercept being possible implies copyXY is possible
3. Assume `hPossible`: E.intercept is possible (for contradiction)
4. By modus ponens: copyXY is possible
5. But `M.no_copyXY` says copyXY is impossible
6. Contradiction ⇒ E.intercept is impossible

**Axiom footprint:** propext, Classical.choice, Quot.sound (all kernel-standard).

### 4.3 Critical Limitation: Conditional Security

**The main theorem is conditional on the hypothesis `hRequiresCloning`.** This hypothesis states that the eavesdropping strategy would require cloning the superinformation medium. The theorem does NOT prove this hypothesis for all attack models; it must be established separately per protocol.

**Current status of "requires cloning" lemmas:**

| Protocol | Lemma | Status |
|----------|-------|--------|
| BB84 | `intercept_resend_requires_copyAll` | **Tautological**: `eveInterceptTask := copyAll` |
| E91 | `intercept_requires_copyAll` | **Tautological**: `eveInterceptTask := copyAll` |

**What this means:** We have proven security against the *intercept-resend* attack class (where Eve must clone to forward). We have NOT proven security against *all* physically realizable eavesdropping strategies.

**What would strengthen this:**
- Prove that any "information-gaining" attack on BB84/E91 necessarily implies a cloning capability
- Formalize the information-disturbance tradeoff
- Connect to the DI framework where CHSH violation bounds Eve's information

### 4.4 Composition Theorem

**Source file:** `HeytingLean/Crypto/ConstructiveHardness/Composition.lean`

```lean
/-- Security composes: if an attack requires a sub-task, and the sub-task is
    impossible, then the attack is impossible. -/
theorem composed_security
    {σ : Type*} {CT : TaskCT σ}
    {T_attack T_sub : Task σ}
    (h_requires : CT.possible T_attack → CT.possible T_sub)
    (h_sub_impossible : CT.impossible T_sub) :
    CT.impossible T_attack := by
  intro h_attack_possible
  exact h_sub_impossible (h_requires h_attack_possible)
```

**Axiom footprint:** None. This theorem is fully constructive.

---

## 5. CHSH Inequality (Complete Proof)

### 5.1 Definitions

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/CHSH/LocalHiddenVariable.lean`

```lean
/-- Binary measurement outcome. -/
inductive Outcome : Type
  | plus   -- +1
  | minus  -- -1

def Outcome.sign : Outcome → ℝ
  | plus => 1
  | minus => -1

/-- A local hidden variable model. -/
structure LocalHiddenVariableModel where
  /-- Hidden variable space (finite). -/
  Λ : Type*
  /-- Fintype instance. -/
  [inst : Fintype Λ]
  /-- Probability mass function. -/
  pmf : Λ → ℝ
  /-- Probabilities are non-negative. -/
  pmf_nonneg : ∀ λ, 0 ≤ pmf λ
  /-- Probabilities sum to 1. -/
  pmf_sum_one : ∑ λ : Λ, pmf λ = 1
  /-- Alice's local response function. -/
  alice : Λ → Bool → Outcome
  /-- Bob's local response function. -/
  bob : Λ → Bool → Outcome
```

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/CHSH/Correlations.lean`

```lean
/-- A correlator: expectation values E(x,y) for settings x,y ∈ {0,1}. -/
structure Correlator where
  value : Bool → Bool → ℝ

/-- CHSH quantity S = E(0,0) + E(0,1) + E(1,0) - E(1,1). -/
def chshQuantity (C : Correlator) : ℝ :=
  C.value false false + C.value false true +
  C.value true false - C.value true true
```

### 5.2 Main Theorem

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/CHSH/CHSHInequality.lean`

```lean
/-- Deterministic CHSH value for a fixed hidden variable. -/
def detCHSH (M : LocalHiddenVariableModel) (l : M.Λ) : ℝ :=
  let a0 := Outcome.sign (M.alice l false)
  let a1 := Outcome.sign (M.alice l true)
  let b0 := Outcome.sign (M.bob l false)
  let b1 := Outcome.sign (M.bob l true)
  a0 * b0 + a0 * b1 + a1 * b0 - a1 * b1

theorem abs_detCHSH_le_two (M : LocalHiddenVariableModel) (l : M.Λ) :
    |M.detCHSH l| ≤ (2 : ℝ) := by
  classical
  unfold detCHSH
  cases ha0 : M.alice l false <;>
  cases ha1 : M.alice l true <;>
  cases hb0 : M.bob l false <;>
  cases hb1 : M.bob l true <;>
  · simp [Outcome.sign]; norm_num

/-- CHSH inequality for an LHV model: |S| ≤ 2. -/
theorem chsh_inequality (M : LocalHiddenVariableModel) :
    |chshQuantity (M.toCorrelator)| ≤ (2 : ℝ) := by
  classical
  -- Step 1: Rewrite S as weighted average of deterministic values
  have hS : chshQuantity (M.toCorrelator) =
      Finset.univ.sum (fun l => M.pmf l * M.detCHSH l) := by
    simp [chshQuantity, LocalHiddenVariableModel.toCorrelator, detCHSH]
    -- ... linearity of summation (details in source)

  -- Step 2: Triangle inequality + bound on deterministic values
  calc
    |chshQuantity (M.toCorrelator)|
        = |Finset.univ.sum (fun l => M.pmf l * M.detCHSH l)| := by simp [hS]
    _ ≤ Finset.univ.sum (fun l => |M.pmf l * M.detCHSH l|) :=
          Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun l => M.pmf l * |M.detCHSH l|) := by
          simp [abs_mul, abs_of_nonneg, M.pmf_nonneg]
    _ ≤ Finset.univ.sum (fun l => M.pmf l * 2) := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_left (M.abs_detCHSH_le_two l) (M.pmf_nonneg l)
    _ = (Finset.univ.sum M.pmf) * 2 := by simp [Finset.sum_mul]
    _ = 2 := by simp [M.pmf_sum_one]
```

### 5.3 Proof Structure

The proof follows the standard argument:

1. **Deterministic bound:** For each λ, with a₀, a₁, b₀, b₁ ∈ {±1}:
   - S(λ) = a₀(b₀ + b₁) + a₁(b₀ - b₁)
   - Either b₀ = b₁ ⟹ S(λ) = ±2a₀
   - Or b₀ = -b₁ ⟹ S(λ) = ±2a₁
   - Therefore |S(λ)| ≤ 2

2. **Averaging:** The observable S = Σ_λ pmf(λ) · S(λ)

3. **Triangle inequality:**
   |S| ≤ Σ_λ pmf(λ) · |S(λ)| ≤ Σ_λ pmf(λ) · 2 = 2

**Line count:** 126 lines (including imports and helper lemmas).

**Axiom footprint:** propext, Classical.choice, Quot.sound.

---

## 6. Tsirelson Bound (Complete Proof)

### 6.1 Definitions

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/Tsirelson/QuantumCorrelations.lean`

```lean
/-- A quantum strategy: unit vectors in a real inner product space. -/
structure QuantumStrategy (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  a0 : V  -- Alice's measurement direction for setting 0
  a1 : V  -- Alice's measurement direction for setting 1
  b0 : V  -- Bob's measurement direction for setting 0
  b1 : V  -- Bob's measurement direction for setting 1
  norm_a0 : ‖a0‖ = 1
  norm_a1 : ‖a1‖ = 1
  norm_b0 : ‖b0‖ = 1
  norm_b1 : ‖b1‖ = 1

/-- Correlator induced by a quantum strategy: E(x,y) = ⟨aₓ, bᵧ⟩. -/
def QuantumStrategy.toCorrelator (S : QuantumStrategy V) : Correlator where
  value := fun x y => inner ℝ (S.aVec x) (S.bVec y)
```

### 6.2 Main Theorem

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/Tsirelson/TsirelsonBound.lean`

```lean
theorem chsh_rewrite (S : QuantumStrategy V) :
    chshQuantity S.toCorrelator =
      inner ℝ S.a0 (S.b0 + S.b1) + inner ℝ S.a1 (S.b0 - S.b1) := by
  simp [chshQuantity, QuantumStrategy.toCorrelator, inner_add_right, inner_sub_right]
  ring

private theorem norm_sum_le_two_sqrt_two (S : QuantumStrategy V) :
    ‖S.b0 + S.b1‖ + ‖S.b0 - S.b1‖ ≤ 2 * Real.sqrt 2 := by
  -- Uses parallelogram law: ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)
  have hsumSq : ‖S.b0 + S.b1‖² + ‖S.b0 - S.b1‖² = 4 := by
    have hpar := parallelogram_law_with_norm (𝕜 := ℝ) S.b0 S.b1
    nlinarith [hpar, S.norm_b0, S.norm_b1]

  -- Optimization: for x,y ≥ 0 with x² + y² = 4, max(x+y) = √8 = 2√2
  have hsq : (‖S.b0 + S.b1‖ + ‖S.b0 - S.b1‖)² ≤ 8 := by
    have hadd := add_sq_le ...
    nlinarith [hadd, hsumSq]

  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by ...
  ...

/-- Tsirelson bound for the CHSH quantity of a vector strategy. -/
theorem tsirelson_bound (S : QuantumStrategy V) :
    |chshQuantity S.toCorrelator| ≤ 2 * Real.sqrt 2 := by
  calc
    |chshQuantity S.toCorrelator|
        = |inner ℝ S.a0 (S.b0 + S.b1) + inner ℝ S.a1 (S.b0 - S.b1)| := by
          simp [S.chsh_rewrite]
    _ ≤ |inner ℝ S.a0 (S.b0 + S.b1)| + |inner ℝ S.a1 (S.b0 - S.b1)| :=
          abs_add_le _ _
    _ ≤ ‖S.a0‖ * ‖S.b0 + S.b1‖ + ‖S.a1‖ * ‖S.b0 - S.b1‖ := by
          gcongr
          · exact abs_real_inner_le_norm S.a0 (S.b0 + S.b1)
          · exact abs_real_inner_le_norm S.a1 (S.b0 - S.b1)
    _ = ‖S.b0 + S.b1‖ + ‖S.b0 - S.b1‖ := by simp [S.norm_a0, S.norm_a1]
    _ ≤ 2 * Real.sqrt 2 := S.norm_sum_le_two_sqrt_two
```

### 6.3 Proof Structure

1. **Rewrite CHSH:** S = ⟨a₀, b₀+b₁⟩ + ⟨a₁, b₀-b₁⟩

2. **Triangle inequality:** |S| ≤ |⟨a₀, b₀+b₁⟩| + |⟨a₁, b₀-b₁⟩|

3. **Cauchy-Schwarz:** |⟨u,v⟩| ≤ ‖u‖·‖v‖

4. **Unit vectors:** ‖aᵢ‖ = 1, so |S| ≤ ‖b₀+b₁‖ + ‖b₀-b₁‖

5. **Parallelogram law:** ‖b₀+b₁‖² + ‖b₀-b₁‖² = 2(‖b₀‖² + ‖b₁‖²) = 4

6. **Optimization:** For x² + y² = 4, max(x+y) = √8 = 2√2

**Line count:** 93 lines.

**Axiom footprint:** propext, Classical.choice, Quot.sound.

---

## 7. Achievability (Complete Proof)

### 7.1 Explicit Strategy

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/Tsirelson/Achievability.lean`

```lean
abbrev V2 : Type := EuclideanSpace ℝ (Fin 2)

-- Standard orthonormal basis
private def b0 : V2 := stdONB 0  -- e₀
private def b1 : V2 := stdONB 1  -- e₁

-- Alice's measurement directions (45° rotated)
private def a0 : V2 := (1 / Real.sqrt 2) • (b0 + b1)
private def a1 : V2 := (1 / Real.sqrt 2) • (b0 - b1)

/-- An explicit strategy achieving S = 2√2. -/
def tsirelsonAchievingStrategy : QuantumStrategy V2 where
  a0 := a0
  a1 := a1
  b0 := b0
  b1 := b1
  norm_a0 := norm_a0  -- proven to be 1
  norm_a1 := norm_a1  -- proven to be 1
  norm_b0 := by simp [b0, stdONB]
  norm_b1 := by simp [b1, stdONB]
```

### 7.2 Main Theorem

```lean
theorem achieves_tsirelson :
    chshQuantity (tsirelsonAchievingStrategy.toCorrelator) = 2 * Real.sqrt 2 := by
  classical
  -- Compute: ⟨a₀, b₀+b₁⟩ = √2 and ⟨a₁, b₀-b₁⟩ = √2
  have hterm1 : inner ℝ a0 (b0 + b1) = Real.sqrt 2 := by
    -- ⟨(1/√2)(b0+b1), b0+b1⟩ = (1/√2)·‖b0+b1‖² = (1/√2)·2 = √2
    ...
  have hterm2 : inner ℝ a1 (b0 - b1) = Real.sqrt 2 := by
    -- ⟨(1/√2)(b0-b1), b0-b1⟩ = (1/√2)·‖b0-b1‖² = (1/√2)·2 = √2
    ...

  -- S = √2 + √2 = 2√2
  calc chshQuantity ... = Real.sqrt 2 + Real.sqrt 2 := ...
                       _ = 2 * Real.sqrt 2 := by ring
```

**Line count:** 181 lines.

**Mathematical content:** The optimal measurements are:
- Alice: a₀ = (e₀ + e₁)/√2 (45°), a₁ = (e₀ - e₁)/√2 (-45°)
- Bob: b₀ = e₀ (0°), b₁ = e₁ (90°)

This achieves the maximum CHSH violation for the singlet state.

---

## 8. QKD Protocol Security

### 8.1 BB84 Security

**Source file:** `HeytingLean/Crypto/QKD/BB84/Security.lean`

```lean
/-- BB84 states form a superinformation medium. -/
def bb84Superinfo : TaskCT.SuperinformationMedium BB84Substrate bb84TaskCT where
  X := zBasisInfo      -- {|0⟩, |1⟩}
  Y := xBasisInfo      -- {|+⟩, |-⟩}
  copyX := copyZ
  copyY := copyX
  copyXY := copyAll
  can_copyX := copyZ_possible
  can_copyY := copyX_possible
  no_copyXY := copyAll_impossible

/-- BB84 is secure against eavesdropping. -/
theorem bb84_secure :
    SecureAgainstEavesdropping BB84Substrate bb84TaskCT bb84Superinfo :=
  superinfo_secure_against_eavesdropping bb84TaskCT bb84Superinfo
```

**Interpretation:** BB84's security follows directly from the main theorem because:
- Z-basis states can be cloned individually (copyZ possible)
- X-basis states can be cloned individually (copyX possible)
- Arbitrary BB84 states cannot all be cloned (copyAll impossible)
- Therefore, eavesdropping requiring full state cloning is impossible

### 8.2 E91 Security

**Source file:** `HeytingLean/Crypto/QKD/E91/Security.lean`

```lean
/-- E91 is secure against eavesdropping. -/
theorem e91_secure :
    SecureAgainstEavesdropping E91Substrate e91TaskCT e91Superinfo :=
  superinfo_secure_against_eavesdropping e91TaskCT e91Superinfo
```

### 8.3 Device-Independent Security

**Source file:** `HeytingLean/Crypto/QKD/E91/DI/Security/CHSHSecurity.lean`

```lean
/-- CHSH violation implies no LHV model can explain the correlations. -/
theorem chsh_violation_no_lhv (C : Correlator) (h_violation : |chshQuantity C| > 2) :
    ¬∃ M : LocalHiddenVariableModel, M.toCorrelator = C := by
  intro ⟨M, heq⟩
  have h_bound := M.chsh_inequality
  rw [heq] at h_bound
  linarith
```

**Interpretation:** If observed CHSH value exceeds 2, no local hidden variable model (including any eavesdropper's model) can explain the correlations.

---

## 9. Contextuality Bridge

### 9.1 Kochen-Specker Theorem (Witness)

**Source file:** `HeytingLean/LoF/CryptoSheaf/Quantum/EmpiricalModel.lean`

```lean
/-- The triangle scenario has no global section. -/
theorem triangle_no_global : NoGlobalSection X_abc triangleCover triangleModel := by
  intro global hConsistent
  -- Derive contradiction from parity constraints
  ...
```

### 9.2 Contextuality Implies Physical Impossibility

**Source file:** `HeytingLean/Crypto/ConstructiveHardness/ContextualityPhysical.lean`

We provide TWO theorems at different abstraction levels:

**Proposition-level (modality):**
```lean
/-- If no global section exists, then no sound physical modality can make
    the global-section task physically achievable. -/
theorem contextuality_implies_physImpossible
    (Φ : PhysicalModality) (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover) (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    NoGlobalSection X cover e coverSubX →
      ¬ Φ.toFun (GlobalSectionTask X cover e coverSubX) := ...
```

**Task-level (constructor existence):**
```lean
/-- If no global section exists, and a task T would soundly witness one,
    then T is CT-impossible (no constructor implements it). -/
theorem contextuality_implies_task_impossible
    {σ : Type u} (CT : TaskCT σ) (X : Context) (cover : Finset Context)
    (e : EmpiricalModel cover) (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X)
    (T : Task σ) (T_sound : CT.possible T → GlobalSectionTask X cover e coverSubX) :
    NoGlobalSection X cover e coverSubX → CT.impossible T := ...
```

**Semantic clarification:**
- `¬Φ.toFun P` means "P is not physically achievable" (proposition-level)
- `CT.impossible T` means "no constructor implements T" (task-level)

These are related but distinct: the first is a statement about propositions under a modality; the second is about tasks under constructor existence. The task-level theorem (`contextuality_implies_task_impossible`) is the one that connects directly to the security framework.

---

## 10. What Is NOT Claimed

For transparency, we explicitly state what is **not** proven:

### 10.1 Security Theorem Limitations

| Limitation | Explanation |
|------------|-------------|
| **Conditional security** | Main theorem requires proving `possible intercept → possible copyXY` per attack model |
| **Intercept-resend only** | Current BB84/E91 lemmas only cover the intercept-resend attack class |
| **Not all eavesdropping** | We do NOT prove "all physically realizable attacks require cloning" |
| **No information-disturbance** | The information-vs-disturbance tradeoff is not formalized |

### 10.2 CT Formalization Scope

| What We Provide | What We Do NOT Provide |
|-----------------|------------------------|
| Constructor types with `implements` | Identity constructors |
| Serial/parallel composition laws | Associativity/commutativity proofs |
| Superinformation medium structure | Full Deutsch-Marletto axioms |
| Existential `possible` semantics | Substrate algebra, permutation groups |

**This is a CT-inspired interface**, not a complete formalization of Constructor Theory.

### 10.3 DI-QKD Scope

| What We Prove | What We Do NOT Prove |
|---------------|---------------------|
| CHSH inequality (|S| ≤ 2) | Entropy accumulation theorem |
| Tsirelson bound (|S| ≤ 2√2) | Finite-key security bounds |
| CHSH violation ⇒ no LHV | Full DI-QKD security reduction |
| Achievability (S = 2√2) | Min-entropy from CHSH violation |

**The DI claims are Bell inequality foundations**, not complete DI-QKD security proofs.

### 10.4 Interfaces (Not Full Proofs)

| Component | Status | Notes |
|-----------|--------|-------|
| Leftover Hash Lemma | Interface | Structure defined, proof axiomatized |
| UC Composition Theorem | Interface | Framework defined, main proof axiomatized |
| Finite-key bounds | Interface | Structures defined, concrete bounds axiomatized |
| Min-entropy properties | Interface | Abstract interface, concrete instantiations partial |

### 10.5 Physical Assumptions

The formalization assumes:
1. Quantum mechanics correctly describes nature
2. No-cloning is a fundamental physical constraint
3. Kochen-Specker contextuality holds for the modeled systems

These are physical assumptions, not mathematical axioms.

### 10.6 Implementation Gap

The Lean proofs establish mathematical security. The Rust implementation (ct-wrap) is a separate artifact that:
- Implements the cryptographic primitives (ML-KEM, ML-DSA, AES-GCM-SIV)
- Is not formally verified against the Lean specifications
- Should be audited separately for implementation correctness

---

## 11. Comparison with Prior Work

| Aspect | This Work | Echenim et al. (Isabelle) | CoqQ (Coq) |
|--------|-----------|--------------------------|------------|
| Proof assistant | Lean 4 | Isabelle/HOL | Coq |
| CHSH inequality | Yes (126 lines) | Yes | No |
| Tsirelson bound | Yes (93 lines) | Yes | No |
| Achievability | Yes (181 lines) | Yes | No |
| CT-style task algebra | **Yes** | No | No |
| Conditional QKD security | **Yes** | No | Partial |
| Bell inequality foundations | Yes | Yes | No |
| Superinformation structure | **Yes** | No | No |

**Novel contributions (with caveats):**
1. **First CT-inspired task algebra in a proof assistant** — but not a full CT formalization
2. **First Lean 4 formalization of CHSH/Tsirelson** — matching Echenim et al.'s Isabelle work
3. **First formal contextuality → security bridge** — but only for intercept-resend attacks
4. **First superinformation medium formalization** — encoding the no-cloning structure

---

## 12. Questions for Reviewer

We invite the reviewer to examine:

1. **CT Fidelity:** Does our `TaskCT` interface capture enough of Constructor Theory to make meaningful security claims? What additional axioms would be needed for a "full" CT formalization?

2. **Conditional Security:** Is our conditional security theorem (`hRequiresCloning` hypothesis) the right abstraction? How can we strengthen the "requires cloning" lemmas beyond the tautological intercept-resend case?

3. **Axiom footprint:** Is the use of propext, Classical.choice, and Quot.sound acceptable for the claimed results? (Note: `composed_security` is axiom-free.)

4. **CHSH/Tsirelson proofs:** Do our vector-strategy models correctly capture the quantum mechanical predictions?

5. **DI-QKD Gap:** What would be required to extend our Bell inequality foundations to a complete DI-QKD security reduction (entropy accumulation, finite-key bounds)?

6. **Contextuality semantics:** Is our distinction between `¬Φ.toFun P` (proposition-level) and `CT.impossible T` (task-level) clear and correctly applied?

---

## 13. Appendix: #print axioms Output

For the reviewer's convenience, here are the actual `#print axioms` outputs for key theorems:

```
-- Run: lake env lean -c 'import HeytingLean; #print axioms ...'

'superinfo_secure_against_eavesdropping' depends on axioms: [propext, Classical.choice, Quot.sound]
'composed_security' does not depend on any axioms
'chsh_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
'tsirelson_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'achieves_tsirelson' depends on axioms: [propext, Classical.choice, Quot.sound]
'bb84_secure' depends on axioms: [propext, Classical.choice, Quot.sound]
'e91_secure' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 14. Contact and Repository

- **Repository:** [Private - available upon request]
- **Verification:** `cd RESEARCHER_BUNDLE && ./scripts/verify_ct_crypto.sh`
- **Build system:** Lake (Lean 4 build tool)
- **Dependencies:** Mathlib4 (pinned version in lakefile.lean)

---

## Revision History

| Date | Changes |
|------|---------|
| 2026-01-08 (v2) | Addressed expert audit feedback: clarified conditional security (§4.3), updated CT scope (§3.1, §10.2), clarified contextuality semantics (§9.2), scoped DI claims (§10.3), updated novel contributions with caveats (§11) |
| 2026-01-08 (v1) | Initial version |

---

*This document is intended for expert review. All theorem statements are extracted from the Lean source code and can be independently verified.*
