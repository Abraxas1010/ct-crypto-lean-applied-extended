import Mathlib.Data.Fin.Tuple.Basic
import HeytingLean.Crypto.QEC.Pauli.PauliGroup

/-!
# Stabilizer codes (interface-first)

We provide enough structure to define syndromes and a decoder, plus a concrete
repetition-code example in `Codes/RepetitionCode.lean`.
-/

namespace HeytingLean.Crypto.QEC.Stabilizer

open HeytingLean.Crypto.QEC.Pauli

/-- A stabilizer group by a finite family of generators. -/
structure StabilizerGroup (n : ℕ) where
  nGen : ℕ
  gen : Fin nGen → Op n
  /-- Pairwise commutation of generators. -/
  gen_commute : ∀ i j, Op.commutes (gen i) (gen j)

/-- An [[n,k,d]] stabilizer code with a chosen decoder. -/
structure StabilizerCode where
  n : ℕ
  k : ℕ
  d : ℕ
  stabilizers : StabilizerGroup n
  /-- A decoder mapping syndrome to a corrective Pauli. -/
  decode : (Fin stabilizers.nGen → Bool) → Op n

namespace StabilizerCode

/-- Syndrome measurement: `true` means the generator anticommutes with the error. -/
def syndrome (C : StabilizerCode) (err : Op C.n) : Fin C.stabilizers.nGen → Bool :=
  fun i => decide (¬ Op.commutes (C.stabilizers.gen i) err)

/-- Apply the code's decoder to the measured syndrome. -/
def correctError (C : StabilizerCode) (err : Op C.n) : Op C.n :=
  C.decode (C.syndrome err)

end StabilizerCode

end HeytingLean.Crypto.QEC.Stabilizer
