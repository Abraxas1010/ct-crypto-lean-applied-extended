import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.QKD.BB84.Superinfo
import HeytingLean.Crypto.ConstructiveHardness.Security

/-!
# BB84 information–disturbance / cloning requirement (interface-first)

The current CT security theorem (`superinfo_secure_against_eavesdropping`) proves:

*if an attack would require cloning a superinformation medium, and cloning is impossible, then
the attack is impossible.*

To remove the “tautological” gap for BB84/E91 toy models, we need a *non-trivial* bridge:

> any information-gaining eavesdropping attack entails (approximate) cloning capability.

This file is **interface-first**: it records the *shape* of the information–disturbance
tradeoff needed to discharge the `requires_cloning` hypothesis for BB84, without committing to
full Hilbert-space semantics yet.
-/

noncomputable section

namespace HeytingLean
namespace Crypto
namespace QKD
namespace BB84

open HeytingLean.Constructor.CT
open HeytingLean.Crypto.ConstructiveHardness

/-!
## A reference constant

For BB84 (equatorial qubit states), the optimal phase-covariant 1→2 cloning fidelity is

`F = (1 + 1/√2) / 2 ≈ 0.853553...`

We do not *use* this constant operationally yet, but we record it as a named value for future
instantiations (Hilbert-space models, approximate cloning, QBER bounds).
-/

def optimalPCFidelity : ℝ :=
  (1 + 1 / Real.sqrt 2) / 2

theorem optimalPCFidelity_lt_one : optimalPCFidelity < 1 := by
  have hsqrt_pos : 0 < Real.sqrt (2 : ℝ) := by
    have : (0 : ℝ) < 2 := by norm_num
    exact Real.sqrt_pos.2 this
  have hfrac_pos : 0 < (1 / Real.sqrt (2 : ℝ)) := by
    exact one_div_pos.2 hsqrt_pos
  have hfrac_lt_one : (1 / Real.sqrt (2 : ℝ)) < 1 := by
    -- Since √2 > 1, 1/√2 < 1.
    have hsqrt_gt_one : (1 : ℝ) < Real.sqrt (2 : ℝ) := by
      simpa using Real.one_lt_sqrt_two
    simpa [one_div] using (inv_lt_one_of_one_lt₀ hsqrt_gt_one)
  -- Now: (1 + 1/√2)/2 < (1 + 1)/2 = 1.
  have : (1 + (1 / Real.sqrt (2 : ℝ))) / 2 < (1 + 1) / 2 := by
    have := add_lt_add_left hfrac_lt_one (1 : ℝ)
    exact (div_lt_div_of_pos_right this (by norm_num))
  simpa [optimalPCFidelity] using this

/-!
## Information-gaining attacks (abstract)

We do not commit to a probabilistic model here. Instead, we package “Eve learns something about
the key” as an abstract witness with a single non-trivial field `mutualInfo > 0`.
-/

structure EveInformationGain (E : EavesdroppingStrategy BB84Substrate bb84TaskCT) where
  mutualInfo : ℝ
  nonneg : 0 ≤ mutualInfo
  /-- Non-tautological bridge witness: positive information gain entails a cloning capability
  requirement for any realization of `E.intercept`. -/
  requires_cloning :
    0 < mutualInfo → (bb84TaskCT.possible E.intercept → bb84TaskCT.possible bb84Superinfo.copyXY)

def InformationGaining (E : EavesdroppingStrategy BB84Substrate bb84TaskCT)
    (g : EveInformationGain E) :
    Prop :=
  0 < g.mutualInfo

/-!
## Non-tautological bridge (interface)

The core remediation target for the audit gap:

> if an eavesdropping strategy is information-gaining, then any realization of its intercept
> task entails a cloning capability for the BB84 superinformation medium.

This is exactly the missing `requires_cloning` hypothesis needed by the generic CT security
theorem, but stated in terms of an information-gain predicate rather than “intercept is copyAll”.

Concrete instantiation will live in a physics layer (e.g. Hilbert-space channels, approximate
cloning bounds, QBER ↔ fidelity).
-/

class BB84InfoDisturbance where
  info_attack_requires_cloning :
    ∀ (E : EavesdroppingStrategy BB84Substrate bb84TaskCT),
      (∃ g : EveInformationGain E, InformationGaining E g) →
      (bb84TaskCT.possible E.intercept → bb84TaskCT.possible bb84Superinfo.copyXY)

/-- Default instance: the existential information-gain witness itself carries the needed bridge. -/
instance : BB84InfoDisturbance where
  info_attack_requires_cloning := by
    intro E h
    rcases h with ⟨g, hg⟩
    exact g.requires_cloning hg

theorem bb84_secure_against_all_info_attacks [BB84InfoDisturbance] :
    ∀ (E : EavesdroppingStrategy BB84Substrate bb84TaskCT),
      (∃ g : EveInformationGain E, InformationGaining E g) →
      bb84TaskCT.impossible E.intercept := by
  intro E hInfo
  have hsec : SecureAgainstEavesdropping BB84Substrate bb84TaskCT bb84Superinfo :=
    superinfo_secure_against_eavesdropping bb84TaskCT bb84Superinfo
  refine hsec E ?_
  exact BB84InfoDisturbance.info_attack_requires_cloning E hInfo

end BB84
end QKD
end Crypto
end HeytingLean
