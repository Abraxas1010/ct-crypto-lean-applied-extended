import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.QKD.BB84.ErrorRate
import HeytingLean.Crypto.SecurityBounds

/-!
# BB84 probabilistic/finite-key security (interface-first)

This layer is intentionally lightweight:
- it reuses the existing QBER development (`BB84.ErrorRate`);
- it packages finite-key bookkeeping (`FiniteKeyBound`);
- it leaves concrete secrecy bounds (entropy, leftover hash lemma) as future work.
-/

namespace HeytingLean.Crypto.QKD.BB84

open HeytingLean.Crypto.SecurityBounds

/-- A BB84 finite-key security statement packaged with a bookkeeping bound. -/
structure BB84FiniteKeySecurity where
  bound : FiniteKeyBound
  /-- Observed QBER (e.g. from `KeyComparison.qberReal`). -/
  observedQBER : ℝ
  observedQBER_nonneg : 0 ≤ observedQBER

/-- The total ε associated to a BB84 finite-key security record. -/
def BB84FiniteKeySecurity.epsilonTotal (S : BB84FiniteKeySecurity) : ℝ :=
  S.bound.epsilon_total

end HeytingLean.Crypto.QKD.BB84
