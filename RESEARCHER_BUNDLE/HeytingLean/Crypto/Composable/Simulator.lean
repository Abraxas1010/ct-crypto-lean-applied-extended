import HeytingLean.Crypto.Composable.IdealFunctionality

/-!
# Universally Composable security (interface-first): simulators

A simulator reconstructs a protocol transcript given only the ideal leakage.
-/

namespace HeytingLean.Crypto.Composable

universe u v w

/-- A simulator for protocol `π` with respect to ideal functionality `F`. -/
structure Simulator (F : IdealFunctionality.{u, v, w}) (π : Protocol F) where
  SimState : Type
  init : SimState
  simulate : F.Leakage → SimState → (π.Message × SimState)

end HeytingLean.Crypto.Composable
