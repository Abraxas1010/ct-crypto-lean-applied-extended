import HeytingLean.Crypto.Composable.Simulator

/-!
# Universally Composable security (interface-first): real/ideal paradigm

We model UC security as:
- a simulator `S` exists
- a chosen indistinguishability predicate holds between the real and ideal executions

All semantics of "indistinguishable" are left abstract by design.
-/

namespace HeytingLean.Crypto.Composable

universe u v w

variable {F : IdealFunctionality.{u, v, w}} (π : Protocol F)

/-- Real execution as an experiment producing an output and transcript. -/
def realExecution : F.Input → F.Output × π.Message :=
  fun i =>
    let (o, m, _s') := π.execute i π.init
    (o, m)

/-- Ideal execution (with simulator) as an experiment producing an output and transcript. -/
def idealExecution (sim : Simulator F π) : F.Input → F.Output × π.Message :=
  fun i =>
    let (o, leak) := F.compute i
    let (m, _s') := sim.simulate leak sim.init
    (o, m)

/-- UC security: real execution is indistinguishable from ideal execution with a simulator. -/
structure UCSecure (F : IdealFunctionality.{u, v, w}) (π : Protocol F) where
  sim : Simulator F π
  Indistinguishable :
    (F.Input → F.Output × π.Message) → (F.Input → F.Output × π.Message) → Prop
  security :
    Indistinguishable (realExecution π) (idealExecution π sim)

end HeytingLean.Crypto.Composable
