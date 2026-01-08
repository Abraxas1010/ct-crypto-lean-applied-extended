import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Min-Entropy (interface-first)

This file provides an abstract interface for min-entropy without importing
measure-theoretic probability. Concrete instances can be supplied later for
finite/discrete distributions.
-/

namespace HeytingLean.Crypto.Information.Entropy

/-- Abstract min-entropy interface. -/
class MinEntropySpace (α : Type*) where
  /-- The type of "distributions" over `α`. -/
  Dist : Type*
  /-- Min-entropy of a distribution (in bits). -/
  Hmin : Dist → ℝ
  /-- Min-entropy is non-negative (interface axiom). -/
  hmin_nonneg : ∀ d, 0 ≤ Hmin d
  /-- Upper bound by log of support size (interface axiom for finite types). -/
  hmin_le_log_card : ∀ {d : Dist} [Fintype α], Hmin d ≤ Real.log (Fintype.card α) / Real.log 2

namespace MinEntropySpace

variable {α : Type*} [MinEntropySpace α]

theorem hmin_nonneg' (d : MinEntropySpace.Dist (α := α)) : 0 ≤ MinEntropySpace.Hmin d :=
  MinEntropySpace.hmin_nonneg d

end MinEntropySpace

end HeytingLean.Crypto.Information.Entropy
