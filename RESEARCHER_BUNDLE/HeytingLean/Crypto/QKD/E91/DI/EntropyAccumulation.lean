import Mathlib.Data.Real.Basic
import HeytingLean.Crypto.Information.Entropy
import HeytingLean.Crypto.SecurityBounds
import HeytingLean.Crypto.QKD.E91.DI.Security.CHSHSecurity

/-!
# Entropy Accumulation (EAT) interface for DI-QKD (interface-first)

The DI layer currently provides the *Bell foundations*:
`|S| > 2` implies the correlator cannot arise from any local hidden-variable model.

To obtain **device-independent key secrecy**, one needs quantitative information-theoretic bounds,
typically of the form:

* CHSH violation ⇒ per-round min-entropy rate bound
* EAT ⇒ total min-entropy lower bound over many rounds

Formalizing EAT in full generality is substantial. This file provides a **minimal, explicit
interface** that lets downstream protocol statements depend on EAT *as a named assumption*,
without introducing global axioms or importing measure-theoretic probability.
-/

namespace HeytingLean
namespace Crypto
namespace QKD
namespace E91
namespace DI

open HeytingLean.Crypto.Information.Entropy
open HeytingLean.Crypto.SecurityBounds
open HeytingLean.Crypto.QKD.E91.DI.CHSH

/-!
## Protocol-level interface

We keep the protocol object abstract: it produces a key distribution indexed by the number of
rounds, and it has an associated CHSH correlator (from which one can compute `|S|`).
-/

structure DIProtocol where
  /-- Key type. -/
  Key : Type
  /-- Abstract min-entropy interface on keys. -/
  [hKey : MinEntropySpace Key]
  /-- Key distribution after `n` rounds. -/
  keyDist : ℕ → MinEntropySpace.Dist (α := Key)
  /-- Observed correlator used to compute the CHSH quantity. -/
  correlator : Correlator

attribute [instance] DIProtocol.hKey

namespace DIProtocol

variable (P : DIProtocol)

def chshValue : ℝ := chshQuantity P.correlator

def violatesCHSH : Prop := |P.chshValue| > 2

end DIProtocol

/-!
## Entropy Accumulation assumption (interface)

`EntropyAccumulation P` packages:
1. a per-round min-entropy rate `rate` extracted from CHSH violation, and
2. a total min-entropy lower bound over `n` rounds.

This matches how DI-QKD proofs are typically structured, while remaining abstract.
-/

class EntropyAccumulation (P : DIProtocol) where
  /-- Min-entropy rate per round (bits/round). -/
  rate : ℝ
  /-- A CHSH violation implies a positive rate. -/
  rate_pos_of_violation : P.violatesCHSH → 0 < rate
  /-- EAT-style lower bound on total min-entropy after `n` rounds. -/
  hmin_lower_bound :
    ∀ n : ℕ,
      P.violatesCHSH → (n : ℝ) * rate ≤ MinEntropySpace.Hmin (P.keyDist n)

namespace EntropyAccumulation

variable (P : DIProtocol)

theorem hmin_nonneg (n : ℕ) : 0 ≤ MinEntropySpace.Hmin (P.keyDist n) :=
  MinEntropySpace.hmin_nonneg (P.keyDist n)

variable [EntropyAccumulation P]

theorem hmin_lower_bound' (n : ℕ) (h : P.violatesCHSH) :
    (n : ℝ) * EntropyAccumulation.rate (P := P) ≤ MinEntropySpace.Hmin (P.keyDist n) :=
  EntropyAccumulation.hmin_lower_bound (P := P) n h

theorem hmin_pos_of_violation (n : ℕ) (hn : 0 < n) (h : P.violatesCHSH) :
    0 < MinEntropySpace.Hmin (P.keyDist n) := by
  have hr : 0 < EntropyAccumulation.rate (P := P) :=
    EntropyAccumulation.rate_pos_of_violation (P := P) h
  have hbound := EntropyAccumulation.hmin_lower_bound' (P := P) n h
  have : 0 < (n : ℝ) * EntropyAccumulation.rate (P := P) := by
    exact mul_pos (by exact_mod_cast hn) hr
  exact lt_of_lt_of_le this hbound

end EntropyAccumulation

end DI
end E91
end QKD
end Crypto
end HeytingLean
