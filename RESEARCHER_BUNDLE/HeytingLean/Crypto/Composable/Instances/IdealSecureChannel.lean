import HeytingLean.Crypto.Composable.IdealFunctionality

/-!
# Ideal functionalities (interface-first): secure channel
-/

namespace HeytingLean.Crypto.Composable.Instances

open HeytingLean.Crypto.Composable

/-- Ideal secure channel functionality `F_SC`. -/
def IdealSecureChannel (msgLen : Nat) : IdealFunctionality where
  Input := Fin msgLen → Bool
  Output := Fin msgLen → Bool
  Leakage := Nat
  compute := fun m => (m, msgLen)

end HeytingLean.Crypto.Composable.Instances
