import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import HeytingLean.Crypto.QEC.Stabilizer.StabilizerCode

/-!
# A tiny QEC witness: 3-qubit bit-flip repetition code

We implement:
- stabilizers: `Z₁Z₂` and `Z₂Z₃` (phase ignored);
- a decoder by syndrome lookup;
- a correctness lemma for single-qubit X errors.

This is purely combinatorial (no matrices, no amplitudes), intended as a minimal
QEC layer for the bundle.
-/

namespace HeytingLean.Crypto.QEC.Codes

open HeytingLean.Crypto.QEC.Pauli
open HeytingLean.Crypto.QEC.Stabilizer

namespace Repetition3

abbrev n : ℕ := 3

def X0 : Op n := ⟨![true, false, false], ![false, false, false]⟩
def X1 : Op n := ⟨![false, true, false], ![false, false, false]⟩
def X2 : Op n := ⟨![false, false, true], ![false, false, false]⟩

def Z01 : Op n := ⟨![false, false, false], ![true, true, false]⟩
def Z12 : Op n := ⟨![false, false, false], ![false, true, true]⟩

def syn00 : Fin 2 → Bool := ![false, false]
def syn10 : Fin 2 → Bool := ![true, false]
def syn11 : Fin 2 → Bool := ![true, true]
def syn01 : Fin 2 → Bool := ![false, true]

def decode : (Fin 2 → Bool) → Op n :=
  fun syn =>
    if syn = syn10 then X0
    else if syn = syn11 then X1
    else if syn = syn01 then X2
    else Op.id n

lemma commute_Z01_Z12 : Op.commutes Z01 Z12 := by
  decide

def stabilizers : StabilizerGroup n where
  nGen := 2
  gen := ![Z01, Z12]
  gen_commute := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide

/-- The 3-qubit repetition code as a stabilizer code with a lookup decoder. -/
def repetitionCode3 : StabilizerCode where
  n := n
  k := 1
  d := 1
  stabilizers := stabilizers
  decode := decode

lemma syndrome_X0 : repetitionCode3.syndrome X0 = syn10 := by
  funext i
  fin_cases i <;> decide

lemma syndrome_X1 : repetitionCode3.syndrome X1 = syn11 := by
  funext i
  fin_cases i <;> decide

lemma syndrome_X2 : repetitionCode3.syndrome X2 = syn01 := by
  funext i
  fin_cases i <;> decide

lemma correct_X0 : repetitionCode3.correctError X0 = X0 := by
  unfold StabilizerCode.correctError
  -- Reduce to decoding the computed syndrome.
  rw [syndrome_X0]
  simp [repetitionCode3, decode, syn10]

lemma correct_X1 : repetitionCode3.correctError X1 = X1 := by
  unfold StabilizerCode.correctError
  rw [syndrome_X1]
  simp [repetitionCode3, decode, syn10, syn11]

lemma correct_X2 : repetitionCode3.correctError X2 = X2 := by
  unfold StabilizerCode.correctError
  rw [syndrome_X2]
  simp [repetitionCode3, decode, syn10, syn11, syn01]

end Repetition3

/-- Repetition code corrects any single-qubit X error (one per qubit). -/
theorem repetitionCode3_corrects_single_X :
    (Repetition3.repetitionCode3.correctError Repetition3.X0 = Repetition3.X0) ∧
    (Repetition3.repetitionCode3.correctError Repetition3.X1 = Repetition3.X1) ∧
    (Repetition3.repetitionCode3.correctError Repetition3.X2 = Repetition3.X2) := by
  exact ⟨Repetition3.correct_X0, Repetition3.correct_X1, Repetition3.correct_X2⟩

end HeytingLean.Crypto.QEC.Codes
