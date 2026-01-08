import HeytingLean.Constructor.CT.Core

/-!
# CT task possibility via constructor existence (sound layer)

`HeytingLean.Constructor.CT.Nucleus` provides an abstract closure operator on *sets* of tasks.
For cryptographic applications (e.g. no-cloning), we also want the constructor-theoretic slogan:

> a task is possible iff there exists a constructor that implements it.

This file provides a minimal, nucleus-free interface for that idea, together with the induced
serial/parallel closure lemmas. It is intentionally lightweight and extraction-friendly.
-/

namespace HeytingLean
namespace Constructor
namespace CT

universe u v

variable {σ : Type u}

/-- A minimal “constructor existence” interface for CT tasks over a substrate `σ`. -/
structure TaskCT (σ : Type u) where
  /-- The type of constructors. -/
  Ctor : Type v
  /-- `implements c T` means constructor `c` can enact task `T`. -/
  implements : Ctor → Task σ → Prop

  /-- Serial composition of constructors (implementing `Task.seq`). -/
  seqCtor : Ctor → Ctor → Ctor
  /-- Parallel composition of constructors (implementing `Task.par`). -/
  parCtor : Ctor → Ctor → Ctor

  /-- If `c₁` implements `T` and `c₂` implements `U`, then `seqCtor c₁ c₂` implements `T;U`. -/
  implements_seq :
    ∀ {c₁ c₂ : Ctor} {T U : Task σ},
      implements c₁ T → implements c₂ U → implements (seqCtor c₁ c₂) (Task.seq T U)

  /-- If `c₁` implements `T` and `c₂` implements `U`, then `parCtor c₁ c₂` implements `T ⊗ U`. -/
  implements_par :
    ∀ {c₁ c₂ : Ctor} {T U : Task σ},
      implements c₁ T → implements c₂ U → implements (parCtor c₁ c₂) (Task.par T U)

namespace TaskCT

variable (CT : TaskCT σ)

/-- A task is possible when some constructor implements it. -/
def possible (T : Task σ) : Prop :=
  ∃ c : CT.Ctor, CT.implements c T

/-- A task is impossible when no constructor implements it. -/
def impossible (T : Task σ) : Prop :=
  ¬ CT.possible T

theorem possible_seq {T U : Task σ} :
    CT.possible T → CT.possible U → CT.possible (Task.seq T U) := by
  intro hT hU
  rcases hT with ⟨c₁, hc₁⟩
  rcases hU with ⟨c₂, hc₂⟩
  refine ⟨CT.seqCtor c₁ c₂, ?_⟩
  exact CT.implements_seq hc₁ hc₂

theorem possible_par {T U : Task σ} :
    CT.possible T → CT.possible U → CT.possible (Task.par T U) := by
  intro hT hU
  rcases hT with ⟨c₁, hc₁⟩
  rcases hU with ⟨c₂, hc₂⟩
  refine ⟨CT.parCtor c₁ c₂, ?_⟩
  exact CT.implements_par hc₁ hc₂

end TaskCT

/-- A slightly strengthened `TaskCT` interface with an explicit identity constructor.

This is a small step toward CT Principles II–V style algebraic completeness:
it makes it possible to talk about “doing nothing” as a constructor, and to
state unit laws at the task level.

We do **not** require definitional equalities on constructors here (e.g. `seqCtor id c = c`),
only that there exists a constructor implementing the identity task.
-/
structure TaskCTFull (σ : Type u) extends TaskCT σ where
  /-- Identity constructor (does nothing). -/
  idCtor : Ctor
  /-- Identity constructor implements the identity task. -/
  implements_id : implements idCtor Task.id

namespace TaskCTFull

variable {σ : Type u} (CT : TaskCTFull σ)

/-- `Task.id` is possible in any `TaskCTFull`. -/
theorem possible_id : CT.toTaskCT.possible (Task.id (σ := σ)) := by
  exact ⟨CT.idCtor, CT.implements_id⟩

end TaskCTFull

end CT
end Constructor
end HeytingLean
