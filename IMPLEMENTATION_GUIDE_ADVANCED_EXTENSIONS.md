# Advanced Extensions Implementation Guide (CT-Crypto Bundle)

This guide specifies extensions to address the current limitations of the CT Crypto formalization.
All extensions must adhere to the bundle's design constraints:

- `sorry`/`admit`: **0**
- strict builds: `lake build --wfail`
- no new global axioms (use *parameters/structures* if assumptions are needed)
- interface-first: prefer lightweight models over heavy probability/quantum semantics

**Status**: Research complete. Implementation specifications follow.

## Implementation Status (RESEARCHER_BUNDLE)

As of **2026-01-07**, the specs in this guide are implemented in
`WIP/CT_Crypto_Repo/RESEARCHER_BUNDLE/` in an interface-first, placeholder-free style:

- **Device-independent E91 (CHSH/Tsirelson)**: `HeytingLean/Crypto/QKD/E91/DI.lean` and `HeytingLean/Crypto/QKD/E91/DI/**`
- **Min-entropy + ε-security bookkeeping**: `HeytingLean/Crypto/Information/Entropy.lean`, `HeytingLean/Crypto/SecurityBounds/SecurityBounds.lean`
- **UC scaffold**: `HeytingLean/Crypto/Composable.lean` (includes `CompositionKit`, `UCSecure`)
- **Hashing + privacy amplification interfaces**: `HeytingLean/Crypto/Information/Hashing.lean`, `HeytingLean/Crypto/Information/PrivacyAmplification.lean`
- **BB84 key-extraction wiring**: `HeytingLean/Crypto/QKD/BB84/KeyExtraction.lean`
- **QEC witness**: `HeytingLean/Crypto/QEC.lean` (includes repetition-code correction lemma)

Strict verification:
- `cd WIP/CT_Crypto_Repo/RESEARCHER_BUNDLE && ./scripts/verify_ct_crypto.sh`

---

## Research Summary: Existing Formalizations

| Topic | Best Existing Work | Proof Assistant | Portability to Lean 4 |
|-------|-------------------|-----------------|----------------------|
| Probability/Measure Theory | Mathlib4 | Lean 4 | Native |
| CHSH/Tsirelson Bound | [AFP TsirelsonBound](https://www.isa-afp.org/entries/TsirelsonBound.html) | Isabelle/HOL | Manual port required |
| UC Framework | [EasyUC](https://eprint.iacr.org/2019/582.pdf) | EasyCrypt | Conceptual port |
| QEC Verification | [CoqQ](https://dl.acm.org/doi/10.1145/3729293), Veri-QEC | Coq | Manual port required |
| Privacy Amplification | None found | — | From scratch |
| Entropy (Shannon) | Mathlib4 (partial) | Lean 4 | Extend existing |
| Quantum Info Theory | [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo) | Lean 4 | Direct dependency |

**Key Sources:**
- [Mathlib4 Probability](https://github.com/leanprover-community/mathlib4) — Markov kernels, distributions
- [Echenim et al. CHSH formalization](https://arxiv.org/abs/2306.12535) — Journal of Automated Reasoning 2024
- [Composable QKD Security (2025)](https://arxiv.org/abs/2505.03874) — High-dimensional QKD proofs
- [Veri-QEC (2025)](https://arxiv.org/abs/2504.07732) — Efficient QEC verification in Coq

---

# Extension 1: Probabilistic Security Bounds

## 1.1 Overview

**Goal**: Formalize security bounds of the form "Eve's information ≤ ε" rather than just "eavesdropping is impossible."

**Approach**: Interface-first. We do NOT import full measure-theoretic probability. Instead:
- Define min-entropy and smooth min-entropy as structures with axiomatized properties
- State security bounds parametrically
- Provide concrete witnesses for finite/discrete cases

## 1.2 File Structure

```
HeytingLean/Crypto/Information/
  Entropy/
    MinEntropy.lean         -- Min-entropy definition and basic properties
    SmoothMinEntropy.lean   -- Smooth min-entropy (parameterized by ε)
    ConditionalEntropy.lean -- H_min(X|E) conditional on adversary's state
  SecurityBounds/
    EpsilonSecurity.lean    -- ε-security definitions
    FiniteKeyBounds.lean    -- Finite-key security bounds (interface)
HeytingLean/Crypto/QKD/BB84/
  ProbabilisticSecurity.lean -- BB84 with ε-security
HeytingLean/Tests/Crypto/
  EntropyBoundsSanity.lean
```

## 1.3 Core Definitions

```lean
/-!
# Min-Entropy (Interface-First)

We define min-entropy abstractly, without importing full measure theory.
Concrete instances can be provided for finite distributions.
-/

namespace HeytingLean.Crypto.Information.Entropy

/-- Abstract min-entropy interface. -/
class MinEntropySpace (α : Type*) where
  /-- The type of distributions over α. -/
  Dist : Type*
  /-- Min-entropy of a distribution (in bits). -/
  Hmin : Dist → ℝ
  /-- Min-entropy is non-negative for non-empty support. -/
  hmin_nonneg : ∀ d, 0 ≤ Hmin d
  /-- Min-entropy is bounded by log of support size (for finite types). -/
  hmin_le_log_card [Fintype α] : ∀ d, Hmin d ≤ Real.log (Fintype.card α) / Real.log 2

/-- Smooth min-entropy: H^ε_min(X). -/
structure SmoothMinEntropy (α : Type*) [MinEntropySpace α] where
  smoothing : ℝ  -- ε parameter
  smoothing_nonneg : 0 ≤ smoothing
  smoothing_lt_one : smoothing < 1
  value : ℝ      -- The smoothed entropy value

/-- Conditional min-entropy H_min(X|E) against adversary E. -/
structure ConditionalMinEntropy (X E : Type*) [MinEntropySpace X] where
  adversarySpace : E → MinEntropySpace.Dist X
  conditionalValue : ℝ
  /-- Conditional entropy ≤ unconditional. -/
  conditioning_decreases : ∀ (d : MinEntropySpace.Dist X), conditionalValue ≤ MinEntropySpace.Hmin d

end HeytingLean.Crypto.Information.Entropy
```

## 1.4 Security Bound Definitions

```lean
namespace HeytingLean.Crypto.SecurityBounds

/-- ε-security: adversary's distinguishing advantage is at most ε. -/
structure EpsilonSecure (Protocol : Type*) where
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  /-- Security holds with probability 1 - ε. -/
  security_probability : ℝ := 1 - epsilon

/-- Finite-key security bound for QKD. -/
structure FiniteKeyBound where
  /-- Number of signals exchanged. -/
  n_signals : ℕ
  /-- Number of test bits. -/
  n_test : ℕ
  /-- Final key length. -/
  key_length : ℕ
  /-- Correctness parameter. -/
  epsilon_cor : ℝ
  /-- Secrecy parameter. -/
  epsilon_sec : ℝ
  /-- Total security parameter. -/
  epsilon_total : ℝ := epsilon_cor + epsilon_sec
  /-- Soundness: total ε is sum of components. -/
  soundness : epsilon_total = epsilon_cor + epsilon_sec := rfl

/-- Key rate formula (asymptotic, interface). -/
def asymptoticKeyRate (qber : ℝ) (h : 0 ≤ qber ∧ qber ≤ 1/2) : ℝ :=
  1 - 2 * binaryEntropy qber
  where
    binaryEntropy (p : ℝ) : ℝ :=
      if p = 0 ∨ p = 1 then 0
      else -p * Real.log p / Real.log 2 - (1 - p) * Real.log (1 - p) / Real.log 2

end HeytingLean.Crypto.SecurityBounds
```

## 1.5 Key Theorems to Prove

```lean
-- These are INTERFACE theorems; concrete proofs require entropy machinery

/-- Asymptotic key rate is positive for QBER < 11%. -/
theorem positive_key_rate_below_threshold (qber : ℝ)
    (h_range : 0 ≤ qber ∧ qber < 0.11) :
    0 < asymptoticKeyRate qber ⟨h_range.1, le_of_lt (lt_of_lt_of_le h_range.2 (by norm_num))⟩

/-- Finite-key rate approaches asymptotic rate as n → ∞. -/
theorem finite_key_convergence (bound : FiniteKeyBound) :
    ∃ (C : ℝ), ∀ n ≥ bound.n_signals,
      |finiteKeyRate n - asymptoticKeyRate (observedQBER n)| ≤ C / Real.sqrt n
```

## 1.6 Implementation Notes

- **DO NOT** import `Mathlib.Probability` unless absolutely necessary
- Use `noncomputable` sections for real-valued entropy functions
- Concrete finite witnesses (e.g., `Fin n → ℝ` distributions) can instantiate the interface
- The Lean-QuantumInfo library may provide useful infrastructure

---

# Extension 2: Composable Security (UC Framework)

## 2.1 Overview

**Goal**: Prove that BB84/E91 are UC-secure, not just "eavesdropping-impossible."

**Approach**: Port the conceptual structure from EasyUC, but stay interface-first.
We define:
- Ideal functionalities as abstract interfaces
- Real/Ideal paradigm via simulation
- Composition theorem as a structure

## 2.2 File Structure

```
HeytingLean/Crypto/Composable/
  IdealFunctionality.lean   -- Abstract ideal functionality
  Simulator.lean            -- Simulator interface
  RealIdealParadigm.lean    -- Real ≈ Ideal definition
  CompositionTheorem.lean   -- UC composition
  Instances/
    IdealKeyExchange.lean   -- F_KE ideal functionality
    IdealSecureChannel.lean -- F_SC ideal functionality
HeytingLean/Crypto/QKD/BB84/
  UCsecurity.lean           -- BB84 UC-realizes F_KE
HeytingLean/Tests/Crypto/
  ComposableSanity.lean
```

## 2.3 Core Definitions

```lean
/-!
# Universally Composable Security (Interface-First)

We model UC security without full simulation-based cryptography machinery.
The key insight: UC security reduces to showing a simulator exists such that
no environment can distinguish real from ideal.
-/

namespace HeytingLean.Crypto.Composable

universe u v

/-- An ideal functionality F takes inputs and produces outputs. -/
structure IdealFunctionality where
  /-- Input type from honest parties. -/
  Input : Type u
  /-- Output type to honest parties. -/
  Output : Type v
  /-- Leakage to adversary (what ideal F reveals). -/
  Leakage : Type*
  /-- The ideal computation. -/
  compute : Input → Output × Leakage

/-- A protocol π in the real world. -/
structure Protocol (F : IdealFunctionality) where
  /-- Internal state type. -/
  State : Type*
  /-- Message type. -/
  Message : Type*
  /-- Protocol execution. -/
  execute : F.Input → State → F.Output × State

/-- A simulator S converts ideal leakage to simulated transcript. -/
structure Simulator (F : IdealFunctionality) (π : Protocol F) where
  /-- Simulator's internal state. -/
  SimState : Type*
  /-- Simulate adversary's view from ideal leakage. -/
  simulate : F.Leakage → SimState → π.Message × SimState

/-- UC-security: real execution is indistinguishable from ideal + simulator. -/
structure UCSecure (F : IdealFunctionality) (π : Protocol F) where
  /-- The simulator witnessing security. -/
  sim : Simulator F π
  /-- Indistinguishability (abstract predicate). -/
  Indistinguishable : (F.Input → F.Output × π.Message) →
                      (F.Input → F.Output × π.Message) → Prop
  /-- Real ≈ Ideal + Sim. -/
  security : Indistinguishable
    (fun i => let (o, s) := π.execute i default; (o, default))
    (fun i => let (o, l) := F.compute i; let (m, _) := sim.simulate l default; (o, m))

end HeytingLean.Crypto.Composable
```

## 2.4 Ideal Functionalities for QKD

```lean
namespace HeytingLean.Crypto.Composable.Instances

/-- Ideal Key Exchange functionality F_KE. -/
def IdealKeyExchange (keyLen : ℕ) : IdealFunctionality where
  Input := Unit  -- Alice and Bob request a key
  Output := Fin keyLen → Bool  -- The shared key
  Leakage := Unit  -- Adversary learns nothing (or just "key generated")
  compute := fun _ => (fun _ => false, ())  -- Ideal: uniform random key

/-- Ideal Secure Channel functionality F_SC. -/
def IdealSecureChannel (msgLen : ℕ) : IdealFunctionality where
  Input := Fin msgLen → Bool  -- Message to send
  Output := Fin msgLen → Bool  -- Message received
  Leakage := ℕ  -- Adversary learns message length only
  compute := fun m => (m, msgLen)

end HeytingLean.Crypto.Composable.Instances
```

## 2.5 Composition Theorem (Interface)

```lean
/-- UC Composition Theorem (interface version).

If π₁ UC-realizes F₁, and π₂ uses F₁ as a subroutine and UC-realizes F₂,
then π₂[π₁/F₁] UC-realizes F₂.
-/
theorem uc_composition
    {F₁ F₂ : IdealFunctionality}
    {π₁ : Protocol F₁} {π₂ : Protocol F₂}
    (h₁ : UCSecure F₁ π₁)
    (h₂ : UCSecure F₂ π₂)
    (h_uses : UsesSubroutine π₂ F₁) :
    UCSecure F₂ (compose π₂ π₁) := by
  -- This is an interface theorem; concrete proof requires
  -- defining compose and showing simulator composition works.
  sorry  -- PLACEHOLDER: Replace with actual proof once infrastructure exists
```

## 2.6 BB84 UC-Security

```lean
namespace HeytingLean.Crypto.QKD.BB84

/-- BB84 as a protocol attempting to realize F_KE. -/
def bb84Protocol (n : ℕ) : Protocol (IdealKeyExchange n) where
  State := BB84State  -- Define appropriately
  Message := List (BB84Basis × Bool)  -- Public transcript
  execute := fun _ s => (extractKey s, nextState s)

/-- BB84 UC-realizes F_KE (modulo ε). -/
theorem bb84_uc_secure (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (sec : UCSecure (IdealKeyExchange n) (bb84Protocol n)),
      -- The simulator is efficient and ε-indistinguishable
      True := by
  -- Interface theorem: construct simulator from no-cloning security
  sorry  -- PLACEHOLDER

end HeytingLean.Crypto.QKD.BB84
```

## 2.7 Implementation Notes

- The full UC framework requires an "environment" (distinguisher) — we abstract this
- Start with "stand-alone" security, extend to UC later
- EasyUC source: https://eprint.iacr.org/2019/582.pdf provides conceptual guidance
- Consider using `Prop`-valued indistinguishability for now (computational version later)

---

# Extension 3: Device-Independent E91 (CHSH/Tsirelson)

## 3.1 Overview

**Goal**: Formalize device-independent security via CHSH inequality violation.

**Existing Work**: The [Isabelle AFP entry TsirelsonBound](https://www.isa-afp.org/entries/TsirelsonBound.html)
provides a complete formalization. We port the key results.

**Key Results to Formalize**:
1. CHSH inequality: Local hidden variables ⟹ |S| ≤ 2
2. Tsirelson bound: Quantum mechanics ⟹ |S| ≤ 2√2
3. Bell state achieves 2√2
4. CHSH violation ⟹ no local hidden variable model ⟹ security

## 3.2 File Structure

```
HeytingLean/Crypto/QKD/E91/DI/
  CHSH/
    Correlations.lean     -- P(a,b|x,y) correlation structure
    LocalHiddenVariable.lean -- LHV model definition
    CHSHInequality.lean   -- |S| ≤ 2 for LHV
  Tsirelson/
    QuantumCorrelations.lean -- Quantum P(a,b|x,y)
    TsirelsonBound.lean   -- |S| ≤ 2√2 for quantum
    Achievability.lean    -- Bell state achieves 2√2
  Security/
    DIProtocol.lean       -- Device-independent E91
    CHSHSecurity.lean     -- CHSH violation ⟹ security
HeytingLean/Tests/Crypto/
  E91DISanity.lean
```

## 3.3 CHSH Inequality Formalization

```lean
/-!
# CHSH Inequality

Reference: Echenim, Mhalla, Mori. "A formalization of the CHSH inequality
and Tsirelson's upper-bound in Isabelle/HOL." JAR 2024.
-/

namespace HeytingLean.Crypto.QKD.E91.DI.CHSH

/-- Binary measurement settings. -/
abbrev Setting := Bool  -- 0 or 1

/-- Binary measurement outcomes. -/
abbrev Outcome := Bool  -- +1 (false) or -1 (true)

/-- A correlation box: probability distribution P(a,b|x,y). -/
structure CorrelationBox where
  /-- Joint probability of outcomes (a,b) given settings (x,y). -/
  prob : Setting → Setting → Outcome → Outcome → ℝ
  /-- Probabilities are non-negative. -/
  prob_nonneg : ∀ x y a b, 0 ≤ prob x y a b
  /-- Normalization: ∑_{a,b} P(a,b|x,y) = 1. -/
  prob_normalized : ∀ x y, (prob x y false false) + (prob x y false true) +
                           (prob x y true false) + (prob x y true true) = 1

/-- Expectation value E(x,y) = ∑_{a,b} (-1)^{a⊕b} P(a,b|x,y). -/
def expectation (box : CorrelationBox) (x y : Setting) : ℝ :=
  (box.prob x y false false) + (box.prob x y true true) -
  (box.prob x y false true) - (box.prob x y true false)

/-- CHSH quantity S = E(0,0) + E(0,1) + E(1,0) - E(1,1). -/
def chshQuantity (box : CorrelationBox) : ℝ :=
  expectation box false false + expectation box false true +
  expectation box true false - expectation box true true

/-- A local hidden variable (LHV) model. -/
structure LocalHiddenVariableModel where
  /-- Hidden variable space. -/
  Lambda : Type*
  /-- Distribution over hidden variables. -/
  dist : Lambda → ℝ
  dist_nonneg : ∀ λ, 0 ≤ dist λ
  /-- Alice's local response function. -/
  alice : Lambda → Setting → Outcome
  /-- Bob's local response function. -/
  bob : Lambda → Setting → Outcome

/-- LHV model induces a correlation box. -/
def lhvToBox [Fintype Λ] (model : LocalHiddenVariableModel) : CorrelationBox where
  prob := fun x y a b =>
    ∑ λ : Λ, if model.alice λ x = a ∧ model.bob λ y = b then model.dist λ else 0
  prob_nonneg := by intro x y a b; apply Finset.sum_nonneg; intro; split_ifs <;> linarith [model.dist_nonneg]
  prob_normalized := by sorry  -- Sum over all (a,b) gives ∑_λ dist(λ) = 1

end HeytingLean.Crypto.QKD.E91.DI.CHSH
```

## 3.4 CHSH Inequality Theorem

```lean
/-- CHSH Inequality: Any LHV model satisfies |S| ≤ 2. -/
theorem chsh_inequality [Fintype Λ] (model : LocalHiddenVariableModel) :
    |chshQuantity (lhvToBox model)| ≤ 2 := by
  -- The proof follows the standard argument:
  -- For each λ, the local contribution to S is bounded by ±2.
  -- Key insight: a₀(b₀ + b₁) + a₁(b₀ - b₁) ∈ {-2, 2} for a_i, b_i ∈ {±1}.
  sorry  -- Port from Isabelle AFP formalization
```

## 3.5 Tsirelson Bound

```lean
namespace HeytingLean.Crypto.QKD.E91.DI.Tsirelson

/-- A quantum correlation box (from measurements on bipartite state). -/
structure QuantumBox extends CorrelationBox where
  /-- There exists a quantum realization. -/
  quantum_realizable : ∃ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : DensityMatrix H) (A₀ A₁ B₀ B₁ : Observable H),
    ∀ x y a b, toCorrelationBox.prob x y a b =
      quantumProb ρ (if x then A₁ else A₀) (if y then B₁ else B₀) a b

/-- Tsirelson Bound: Any quantum correlation satisfies |S| ≤ 2√2. -/
theorem tsirelson_bound (box : QuantumBox) :
    |chshQuantity box.toCorrelationBox| ≤ 2 * Real.sqrt 2 := by
  -- Proof uses operator norm bounds on observables.
  -- Reference: Tsirelson (1980), formalized in Isabelle AFP.
  sorry  -- Port from Isabelle AFP formalization

/-- Bell state achieves the Tsirelson bound. -/
theorem bell_state_achieves_tsirelson :
    ∃ (box : QuantumBox), chshQuantity box.toCorrelationBox = 2 * Real.sqrt 2 := by
  -- Construct Bell state |Φ⁺⟩ and optimal measurements.
  sorry  -- Port from Isabelle AFP formalization

end HeytingLean.Crypto.QKD.E91.DI.Tsirelson
```

## 3.6 Device-Independent Security

```lean
namespace HeytingLean.Crypto.QKD.E91.DI.Security

/-- CHSH violation witnesses absence of LHV model. -/
theorem chsh_violation_no_lhv (box : CorrelationBox)
    (h_violation : |chshQuantity box| > 2) :
    ¬ ∃ [Fintype Λ] (model : @LocalHiddenVariableModel Λ),
      lhvToBox model = box := by
  intro ⟨_, model, heq⟩
  have h_bound := chsh_inequality model
  rw [heq] at h_bound
  linarith

/-- Device-independent E91 security: CHSH violation ⟹ eavesdropping detected. -/
theorem di_e91_secure (box : CorrelationBox)
    (h_violation : chshQuantity box > 2) :
    -- Any eavesdropper would reduce the CHSH value (monogamy of entanglement)
    ∀ (eve_info : ℝ), eve_info > 0 →
      ∃ (reduced_chsh : ℝ), reduced_chsh < chshQuantity box := by
  -- This follows from monogamy of entanglement.
  -- Full proof requires entropy bounds.
  sorry  -- Interface: concrete proof needs quantum entropy

end HeytingLean.Crypto.QKD.E91.DI.Security
```

## 3.7 Implementation Notes

- The Isabelle AFP entry uses 4 main theory files; we reorganize for Lean
- Key dependency: density matrices and operator norms from Mathlib
- Consider importing [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo) for quantum infrastructure
- Start with finite-dimensional Hilbert spaces (avoid infinite-dim complications)

---

# Extension 4: Privacy Amplification / Leftover Hash Lemma

## 4.1 Overview

**Goal**: Formalize the leftover hash lemma (LHL) which enables privacy amplification.

**Status**: No existing formalization found in any proof assistant as of 2025.

**Key Result**: If X has min-entropy k, and H is a universal hash family,
then H(X) is ε-close to uniform where ε ≈ 2^{-(k-ℓ)/2} for output length ℓ.

## 4.2 File Structure

```
HeytingLean/Crypto/Information/
  Hashing/
    UniversalHash.lean      -- Universal hash family definition
    TwoUniversal.lean       -- 2-universal hash families
    StrongExtractor.lean    -- Strong randomness extractor
  PrivacyAmplification/
    LeftoverHashLemma.lean  -- Main LHL statement
    PrivacyAmplification.lean -- Application to QKD
HeytingLean/Crypto/QKD/BB84/
  KeyExtraction.lean        -- BB84 key extraction via LHL
HeytingLean/Tests/Crypto/
  PrivacyAmpSanity.lean
```

## 4.3 Universal Hash Family

```lean
/-!
# Universal Hash Families

A family of hash functions H is 2-universal if for distinct x ≠ y,
Pr_h[h(x) = h(y)] ≤ 1/|Range|.
-/

namespace HeytingLean.Crypto.Information.Hashing

/-- A hash family from domain D to range R, parameterized by seed S. -/
structure HashFamily (D R S : Type*) where
  hash : S → D → R

/-- 2-universal hash family. -/
class TwoUniversal (D R S : Type*) [Fintype R] [Fintype S]
    extends HashFamily D R S where
  /-- Collision probability bound. -/
  collision_bound : ∀ (x y : D), x ≠ y →
    (Finset.filter (fun s => hash s x = hash s y) Finset.univ).card ≤
    Fintype.card S / Fintype.card R

/-- Example: Linear hash family over finite fields. -/
def linearHash (p : ℕ) [hp : Fact (Nat.Prime p)] :
    HashFamily (ZMod p) (ZMod p) (ZMod p × ZMod p) where
  hash := fun ⟨a, b⟩ x => a * x + b

instance linearHash_twoUniversal (p : ℕ) [hp : Fact (Nat.Prime p)] :
    TwoUniversal (ZMod p) (ZMod p) (ZMod p × ZMod p) where
  toHashFamily := linearHash p
  collision_bound := by
    intro x y hne
    -- For ax + b = ay + b, need a(x-y) = 0, but x ≠ y so a = 0.
    -- Only 1/p fraction of seeds have a = 0.
    sorry  -- Standard argument

end HeytingLean.Crypto.Information.Hashing
```

## 4.4 Leftover Hash Lemma

```lean
namespace HeytingLean.Crypto.Information.PrivacyAmplification

open Hashing Entropy

/-- Statistical distance between distributions. -/
def statDistance {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1/2) * ∑ x, |p x - q x|

/-- Uniform distribution on finite type. -/
def uniform {α : Type*} [Fintype α] : α → ℝ :=
  fun _ => 1 / Fintype.card α

/-- Leftover Hash Lemma (Interface Version).

If X has min-entropy at least k bits, and H is 2-universal with output ℓ bits,
then (H(s), H_s(X)) is ε-close to (H(s), U_ℓ) where ε = 2^{-(k-ℓ)/2}.
-/
theorem leftover_hash_lemma
    {D R S : Type*} [Fintype D] [Fintype R] [Fintype S]
    [TwoUniversal D R S]
    (X : D → ℝ)  -- Distribution on domain
    (hX_dist : ∀ x, 0 ≤ X x)
    (hX_norm : ∑ x, X x = 1)
    (k : ℝ)  -- Min-entropy of X
    (hk : minEntropy X ≥ k)
    (ℓ : ℝ)  -- Output length in bits
    (hℓ : ℓ = Real.log (Fintype.card R) / Real.log 2) :
    let ε := Real.rpow 2 (-(k - ℓ) / 2)
    statDistance (jointDist X (TwoUniversal.hash (D := D)))
                 (productDist (seedDist S) (uniform (α := R))) ≤ ε := by
  -- The proof requires:
  -- 1. Expand statistical distance
  -- 2. Use 2-universality to bound collision probability
  -- 3. Relate collision probability to min-entropy
  sorry  -- Major theorem: requires careful probability argument

end HeytingLean.Crypto.Information.PrivacyAmplification
```

## 4.5 Application to QKD

```lean
namespace HeytingLean.Crypto.QKD.BB84

/-- Privacy amplification for BB84: extract secure key from raw key. -/
def privacyAmplification
    (rawKey : Fin n → Bool)
    (eveInfo : ℝ)  -- Bound on Eve's information
    (targetSecrecy : ℝ) :
    { finalKey : Fin m → Bool // m ≤ n ∧
      -- Final key is targetSecrecy-close to uniform given Eve's info
      True } := by
  -- Use leftover hash lemma with:
  -- k = n - eveInfo (remaining min-entropy)
  -- ℓ = k - 2 * log(1/targetSecrecy)
  sorry  -- Construction using LHL

end HeytingLean.Crypto.QKD.BB84
```

## 4.6 Implementation Notes

- This is the most challenging extension: no prior formalization exists
- Start with finite/discrete probability only
- The key inequality is the "collision probability" bound
- Consider simplifying to specific hash families (e.g., Toeplitz matrices)
- Mathlib's `Fintype` and `Finset.sum` provide the combinatorial backbone

---

# Extension 5: Quantum Error Correction

## 5.1 Overview

**Goal**: Formalize stabilizer codes and basic QEC sufficient for QKD.

**Existing Work**:
- [CoqQ](https://www.researchgate.net/publication/367048417_CoqQ_Foundational_Verification_of_Quantum_Programs) in Coq
- [Veri-QEC](https://arxiv.org/abs/2504.07732) (2025) — automated QEC verification

**Scope for CT-Crypto**: We need only enough QEC to justify error correction in QKD,
not full fault-tolerant quantum computation.

## 5.2 File Structure

```
HeytingLean/Crypto/QEC/
  Pauli/
    PauliGroup.lean        -- Pauli matrices and group structure
    PauliString.lean       -- n-qubit Pauli strings
  Stabilizer/
    StabilizerGroup.lean   -- Stabilizer formalism
    StabilizerCode.lean    -- [[n,k,d]] codes
    Syndrome.lean          -- Syndrome measurement
  Codes/
    RepetitionCode.lean    -- [[3,1,1]] repetition code
    SteaneCode.lean        -- [[7,1,3]] Steane code (if needed)
  Decoding/
    SyndromeDecoding.lean  -- Basic syndrome decoding
HeytingLean/Crypto/QKD/
  ErrorCorrection.lean     -- QEC layer for QKD
HeytingLean/Tests/Crypto/
  QECSanity.lean
```

## 5.3 Pauli Group

```lean
/-!
# Pauli Group

The Pauli group on n qubits is generated by tensor products of {I, X, Y, Z}.
-/

namespace HeytingLean.Crypto.QEC.Pauli

/-- Single-qubit Pauli operators. -/
inductive Pauli1 : Type
  | I  -- Identity
  | X  -- Bit flip
  | Y  -- Bit-phase flip
  | Z  -- Phase flip
  deriving DecidableEq, Repr

/-- Phase factor ∈ {1, -1, i, -i}. -/
inductive Phase : Type
  | one      -- +1
  | neg_one  -- -1
  | i        -- +i
  | neg_i    -- -i
  deriving DecidableEq, Repr

/-- Pauli group element: phase × tensor product of Pauli1. -/
structure PauliN (n : ℕ) where
  phase : Phase
  ops : Fin n → Pauli1
  deriving DecidableEq, Repr

namespace Pauli1

/-- Multiplication table for single-qubit Paulis. -/
def mul : Pauli1 → Pauli1 → Phase × Pauli1
  | I, p => (Phase.one, p)
  | p, I => (Phase.one, p)
  | X, X => (Phase.one, I)
  | Y, Y => (Phase.one, I)
  | Z, Z => (Phase.one, I)
  | X, Y => (Phase.i, Z)
  | Y, X => (Phase.neg_i, Z)
  | Y, Z => (Phase.i, X)
  | Z, Y => (Phase.neg_i, X)
  | Z, X => (Phase.i, Y)
  | X, Z => (Phase.neg_i, Y)

/-- Paulis anticommute: XY = -YX, etc. -/
theorem anticommute_XY : mul X Y = (Phase.i, Z) ∧ mul Y X = (Phase.neg_i, Z) := by
  simp [mul]

end Pauli1

/-- n-qubit Pauli group multiplication. -/
def PauliN.mul {n : ℕ} (p q : PauliN n) : PauliN n where
  phase := Phase.mul p.phase (Phase.mul_all (fun i => (Pauli1.mul (p.ops i) (q.ops i)).1))
  ops := fun i => (Pauli1.mul (p.ops i) (q.ops i)).2

instance {n : ℕ} : Mul (PauliN n) := ⟨PauliN.mul⟩

end HeytingLean.Crypto.QEC.Pauli
```

## 5.4 Stabilizer Codes

```lean
namespace HeytingLean.Crypto.QEC.Stabilizer

open Pauli

/-- A stabilizer group is an abelian subgroup of the Pauli group not containing -I. -/
structure StabilizerGroup (n : ℕ) where
  /-- Generators of the stabilizer group. -/
  generators : List (PauliN n)
  /-- All generators have phase +1. -/
  generators_phase : ∀ g ∈ generators, g.phase = Phase.one
  /-- Generators commute pairwise. -/
  generators_commute : ∀ g h, g ∈ generators → h ∈ generators → g * h = h * g

/-- An [[n,k,d]] stabilizer code. -/
structure StabilizerCode where
  /-- Number of physical qubits. -/
  n : ℕ
  /-- Number of logical qubits. -/
  k : ℕ
  /-- Distance (minimum weight of non-trivial logical operator). -/
  d : ℕ
  /-- The stabilizer group (n-k independent generators). -/
  stabilizers : StabilizerGroup n
  /-- Number of generators. -/
  n_generators : stabilizers.generators.length = n - k

/-- Syndrome: measurement outcome of stabilizer generators. -/
def syndrome {n : ℕ} (code : StabilizerCode) (error : PauliN n) :
    Fin code.stabilizers.generators.length → Bool :=
  fun i =>
    let g := code.stabilizers.generators[i]
    -- +1 eigenvalue (commutes) → false, -1 eigenvalue (anticommutes) → true
    commutes g error = false
  where
    commutes (g e : PauliN n) : Bool := g * e = e * g

/-- Error correction: infer error from syndrome. -/
def correctError {n : ℕ} (code : StabilizerCode)
    (syn : Fin (n - code.k) → Bool) : PauliN n :=
  -- Lookup table or minimum-weight decoder
  sorry  -- Implementation depends on specific code

end HeytingLean.Crypto.QEC.Stabilizer
```

## 5.5 Repetition Code Example

```lean
namespace HeytingLean.Crypto.QEC.Codes

open Pauli Stabilizer

/-- The [[3,1,1]] bit-flip repetition code. -/
def repetitionCode3 : StabilizerCode where
  n := 3
  k := 1
  d := 1
  stabilizers := {
    generators := [
      ⟨Phase.one, ![Pauli1.Z, Pauli1.Z, Pauli1.I]⟩,  -- Z₁Z₂
      ⟨Phase.one, ![Pauli1.I, Pauli1.Z, Pauli1.Z]⟩   -- Z₂Z₃
    ]
    generators_phase := by simp
    generators_commute := by
      intro g h hg hh
      -- ZZ and ZZ commute
      sorry
  }
  n_generators := by simp

/-- Repetition code corrects single bit-flip errors. -/
theorem repetitionCode3_corrects_single_X :
    ∀ i : Fin 3,
      let error := singleX i
      let syn := syndrome repetitionCode3 error
      correctError repetitionCode3 syn = error := by
  sorry  -- Verify syndrome table

end HeytingLean.Crypto.QEC.Codes
```

## 5.6 QEC for QKD

```lean
namespace HeytingLean.Crypto.QKD

/-- Error correction in QKD: reconcile Alice and Bob's raw keys. -/
structure KeyReconciliation where
  /-- Classical error correction code. -/
  code : LinearCode  -- Or use stabilizer formalism
  /-- Communication cost (bits leaked to Eve). -/
  leakage : ℕ
  /-- Failure probability. -/
  failure_prob : ℝ

/-- Error correction preserves security if leakage is accounted for. -/
theorem error_correction_secure
    (rawKeyEntropy : ℝ)
    (reconciliation : KeyReconciliation)
    (h_entropy : rawKeyEntropy > reconciliation.leakage) :
    ∃ (remainingEntropy : ℝ),
      remainingEntropy ≥ rawKeyEntropy - reconciliation.leakage ∧
      remainingEntropy > 0 := by
  use rawKeyEntropy - reconciliation.leakage
  constructor
  · linarith
  · linarith

end HeytingLean.Crypto.QKD
```

## 5.7 Implementation Notes

- For QKD, we primarily need classical error correction (LDPC, etc.)
- Quantum stabilizer codes are relevant for quantum repeaters
- Start with the repetition code as a minimal example
- CoqQ provides a reference implementation for the quantum parts
- Veri-QEC (2025) shows how to automate verification for specific codes

---

# Verification Protocol

After implementing each extension, verify:

```bash
# From lean/ directory
./scripts/guard_no_sorry.sh
lake build --wfail

# Check specific modules
lake build HeytingLean.Crypto.Information.Entropy --wfail
lake build HeytingLean.Crypto.Composable --wfail
lake build HeytingLean.Crypto.QKD.E91.DI --wfail
lake build HeytingLean.Crypto.Information.PrivacyAmplification --wfail
lake build HeytingLean.Crypto.QEC --wfail

# Run sanity tests
lake build HeytingLean.Tests.Crypto.EntropyBoundsSanity --wfail
lake build HeytingLean.Tests.Crypto.ComposableSanity --wfail
lake build HeytingLean.Tests.Crypto.E91DISanity --wfail
lake build HeytingLean.Tests.Crypto.PrivacyAmpSanity --wfail
lake build HeytingLean.Tests.Crypto.QECSanity --wfail
```

---

# Implementation Priority

Based on dependencies and impact:

| Priority | Extension | Dependencies | Estimated Complexity |
|----------|-----------|--------------|---------------------|
| 1 | CHSH/Tsirelson (§3) | Mathlib linear algebra | Medium (port from Isabelle) |
| 2 | Min-Entropy (§1.3) | Mathlib reals | Low (interface-first) |
| 3 | Stabilizer Codes (§5.3-5.4) | Mathlib algebra | Medium |
| 4 | Leftover Hash (§4) | Min-Entropy | High (no prior work) |
| 5 | UC Framework (§2) | All above | High (conceptual complexity) |

**Recommended order**: 3.3-3.5 (CHSH) → 1.3-1.4 (Entropy) → 5.3-5.5 (QEC) → 4.3-4.4 (LHL) → 2.3-2.5 (UC)

---

# References

1. [Mathlib4 Probability](https://github.com/leanprover-community/mathlib4) — Markov kernels, distributions
2. [Echenim et al. (2024)](https://link.springer.com/article/10.1007/s10817-023-09689-9) — CHSH/Tsirelson in Isabelle
3. [AFP TsirelsonBound](https://www.isa-afp.org/entries/TsirelsonBound.html) — Formal proofs
4. [EasyUC](https://eprint.iacr.org/2019/582.pdf) — UC proofs in EasyCrypt
5. [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo) — Quantum info in Lean 4
6. [Veri-QEC (2025)](https://arxiv.org/abs/2504.07732) — QEC verification in Coq
7. [Composable QKD (2025)](https://arxiv.org/abs/2505.03874) — High-dimensional QKD proofs
8. [Leftover Hash Lemma](https://en.wikipedia.org/wiki/Leftover_hash_lemma) — Background
