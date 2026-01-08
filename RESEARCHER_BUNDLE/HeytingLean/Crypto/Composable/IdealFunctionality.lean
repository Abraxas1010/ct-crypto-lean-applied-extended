/-!
# Universally Composable security (interface-first): ideal functionalities and protocols

This folder provides a lightweight UC-shaped interface intended for later refinement.
We do **not** commit to a probability framework or computational indistinguishability here.
-/

namespace HeytingLean.Crypto.Composable

universe u v w

/-- An ideal functionality `F` takes an input and produces an output, plus some leakage. -/
structure IdealFunctionality where
  Input : Type u
  Output : Type v
  Leakage : Type w
  compute : Input → Output × Leakage

/-- A (single-shot) protocol in the real world, attempting to realize an ideal functionality. -/
structure Protocol (F : IdealFunctionality.{u, v, w}) where
  State : Type
  Message : Type
  init : State
  execute : F.Input → State → (F.Output × Message × State)

end HeytingLean.Crypto.Composable
