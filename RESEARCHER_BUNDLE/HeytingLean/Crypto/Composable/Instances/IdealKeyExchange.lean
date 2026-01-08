import HeytingLean.Crypto.Composable.IdealFunctionality

/-!
# Ideal functionalities (interface-first): key exchange

This is intentionally lightweight: we do not model randomness here.
-/

namespace HeytingLean.Crypto.Composable.Instances

open HeytingLean.Crypto.Composable

/-- Ideal key exchange functionality `F_KE`. -/
def IdealKeyExchange (keyLen : Nat) : IdealFunctionality where
  Input := Unit
  Output := Fin keyLen → Bool
  Leakage := Unit
  compute := fun _ => (fun _ => false, ())

end HeytingLean.Crypto.Composable.Instances
