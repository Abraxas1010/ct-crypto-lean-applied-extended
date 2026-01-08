import Mathlib.Data.Fin.Basic

/-!
# A lightweight Pauli formalism (interface-first)

We model n-qubit Paulis using the standard binary symplectic representation:
an operator is a pair of bit-vectors `(x, z)` over `Fin n`.

This is sufficient to:
- define commutation via the symplectic inner product mod 2;
- build simple stabilizer-code examples (e.g. repetition code) without matrices.
-/

namespace HeytingLean.Crypto.QEC.Pauli

/-- An n-qubit Pauli operator (phase ignored): binary symplectic form. -/
structure Op (n : ℕ) where
  x : Fin n → Bool
  z : Fin n → Bool

namespace Op

variable {n : ℕ}

/-- Identity operator. -/
def id (n : ℕ) : Op n :=
  ⟨fun _ => false, fun _ => false⟩

/-- Multiply Paulis by XOR-ing the symplectic components (phase ignored). -/
def mul (p q : Op n) : Op n :=
  ⟨fun i => Bool.xor (p.x i) (q.x i), fun i => Bool.xor (p.z i) (q.z i)⟩

instance : Mul (Op n) := ⟨mul⟩

/-- Symplectic bit at index `i`. -/
def sympBit (p q : Op n) (i : Fin n) : Bool :=
  Bool.xor (p.x i && q.z i) (p.z i && q.x i)

/-- Symplectic inner product count (number of `i` where `sympBit` is true). -/
def sympCount (p q : Op n) : Nat :=
  (List.ofFn (fun i : Fin n => sympBit p q i)).foldl (fun acc b => acc + (if b then 1 else 0)) 0

/-- Two Paulis commute iff the symplectic count is even. -/
def commutes (p q : Op n) : Prop :=
  sympCount p q % 2 = 0

instance (p q : Op n) : Decidable (commutes p q) := by
  dsimp [commutes]
  infer_instance

@[simp] theorem sympBit_of_x_false_left (p q : Op n) (i : Fin n) (hx : p.x i = false) :
    sympBit p q i = (p.z i && q.x i) := by
  simp [sympBit, hx]

@[simp] theorem sympBit_of_z_false_left (p q : Op n) (i : Fin n) (hz : p.z i = false) :
    sympBit p q i = (p.x i && q.z i) := by
  simp [sympBit, hz]

/-- Single-qubit X error at position `i`. -/
def singleX {n : ℕ} (i : Fin n) : Op n :=
  ⟨fun j => decide (j = i), fun _ => false⟩

/-- Single-qubit Z operator at position `i`. -/
def singleZ {n : ℕ} (i : Fin n) : Op n :=
  ⟨fun _ => false, fun j => decide (j = i)⟩

end Op

end HeytingLean.Crypto.QEC.Pauli
