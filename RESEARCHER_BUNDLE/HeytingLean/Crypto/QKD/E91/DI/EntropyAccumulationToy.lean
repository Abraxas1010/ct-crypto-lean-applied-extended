import Mathlib.Data.Finite.Defs
import HeytingLean.Crypto.QKD.E91.DI.EntropyAccumulation
import HeytingLean.Crypto.QKD.E91.DI.Tsirelson.Achievability

/-!
# A toy Entropy Accumulation instantiation (concrete, interface-compatible)

This file provides a *concrete* `EntropyAccumulation` instance for a specific protocol built from
the Tsirelson-achieving correlator, while remaining within the project's interface-first entropy
setup (no measure theory).

Important: this is an **example instantiation**. It should not be read as a full DI-QKD security
proof; rather, it demonstrates how one can plug an EAT-style lower bound into the existing DI
interfaces without introducing new global axioms.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91
namespace DI

open HeytingLean.Crypto.Information.Entropy
open HeytingLean.Crypto.QKD.E91.DI.CHSH
open HeytingLean.Crypto.QKD.E91.DI.Tsirelson

/-!
## A minimal min-entropy space on `Nat`

We use `Nat` as a provably infinite key type. For infinite types, the `hmin_le_log_card` axiom of
`MinEntropySpace` is vacuous: assuming `[Fintype Nat]` contradicts `[Infinite Nat]`.
-/

instance : MinEntropySpace ℕ where
  Dist := { hmin : ℝ // 0 ≤ hmin }
  Hmin := fun d => d.1
  hmin_nonneg := fun d => d.2
  hmin_le_log_card := by
    intro d instFintype
    -- `Nat` is infinite, hence cannot be finite.
    have instFinite : Finite ℕ := by infer_instance
    exact (False.elim (not_finite ℕ))

/-!
## A concrete rate extracted from Tsirelson's CHSH value

For the Tsirelson-achieving strategy, `|S| = 2√2`. We define a simple positive rate:

`rate := (2√2 - 2) / 4`.
-/

noncomputable def tsirelsonRate : ℝ :=
  (2 * Real.sqrt 2 - 2) / 4

theorem tsirelsonRate_pos : 0 < tsirelsonRate := by
  have hs : (2 : ℝ) < 2 * Real.sqrt 2 := by
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      simpa using Real.one_lt_sqrt_two
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    simpa [two_mul] using (mul_lt_mul_of_pos_left h1 h2)
  have hnum : 0 < (2 * Real.sqrt 2 - 2) := by linarith
  have hden : (0 : ℝ) < 4 := by norm_num
  exact div_pos hnum hden

/-!
## A toy protocol and its EntropyAccumulation instance

We package:
- the Tsirelson-achieving correlator;
- a key distribution returning a certified nonnegative min-entropy value `(n : ℝ) * rate`.

Then the EAT lower bound is definitional.
-/

noncomputable def tsirelsonToyProtocol : DIProtocol where
  Key := ℕ
  hKey := by infer_instance
  keyDist := fun n =>
    (show MinEntropySpace.Dist (α := ℕ) from
      ⟨(n : ℝ) * tsirelsonRate, by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have hr : 0 ≤ tsirelsonRate := le_of_lt tsirelsonRate_pos
        exact mul_nonneg hn hr⟩)
  correlator := Tsirelson.Examples.tsirelsonAchievingStrategy.toCorrelator

theorem tsirelsonToyProtocol_violatesCHSH : tsirelsonToyProtocol.violatesCHSH := by
  -- Use the explicit `S = 2√2` computation.
  have hS : DIProtocol.chshValue tsirelsonToyProtocol =
      2 * Real.sqrt 2 := by
    simp [DIProtocol.chshValue, tsirelsonToyProtocol,
      Tsirelson.Examples.achieves_tsirelson]
  -- Since √2 > 1, we have 2√2 > 2.
  have hs : (2 : ℝ) < 2 * Real.sqrt 2 := by
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      simpa using Real.one_lt_sqrt_two
    have h2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    simpa [two_mul] using (mul_lt_mul_of_pos_left h1 h2)
  have hSpos : 0 < DIProtocol.chshValue tsirelsonToyProtocol := by
    -- `2 * √2 > 0`.
    have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have : 0 < 2 * Real.sqrt (2 : ℝ) := by nlinarith
    rw [hS]
    exact this
  have hSpos' : 0 < (2 * Real.sqrt 2) := by
    -- Rewrite the already-established positivity of `S` using `S = 2√2`.
    have hSpos0 := hSpos
    rw [hS] at hSpos0
    exact hSpos0
  have habs : |DIProtocol.chshValue tsirelsonToyProtocol| = 2 * Real.sqrt 2 := by
    rw [hS, abs_of_pos hSpos']
  -- Conclude `|S| > 2`.
  have : |DIProtocol.chshValue tsirelsonToyProtocol| > 2 := by
    simpa [habs] using hs
  simpa [DIProtocol.violatesCHSH] using this

noncomputable instance : EntropyAccumulation tsirelsonToyProtocol where
  rate := tsirelsonRate
  rate_pos_of_violation := by
    intro _
    exact tsirelsonRate_pos
  hmin_lower_bound := by
    intro n _
    -- Definitional: `Hmin (keyDist n) = (n : ℝ) * rate`.
    simp [tsirelsonToyProtocol, tsirelsonRate]
    exact le_rfl

end DI
end E91
end QKD
end Crypto
end HeytingLean
