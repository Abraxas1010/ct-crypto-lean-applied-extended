# Next Phase: QKD Extensions (Post-BB84)

This is a running implementation checklist for extending the CT-crypto formalization beyond BB84, while keeping:
- `sorry`/`admit`: **0**
- strict builds: `lake build --wfail`
- clean extraction boundaries (core CT vs. crypto instantiations)

## 0) Inventory (What We Reuse)

- CT core tasks + constructor existence: `HeytingLean/Constructor/CT/Core.lean`, `HeytingLean/Constructor/CT/TaskExistence.lean`
- Superinformation interface: `HeytingLean/Constructor/CT/InformationSound.lean`
- No-cloning ⇒ security meta-theorem: `HeytingLean/Crypto/ConstructiveHardness/Security.lean`
- Composition transfer: `HeytingLean/Crypto/ConstructiveHardness/Composition.lean`
- BB84 concrete instantiation:
  - states/tasks/constructors/superinfo/security: `HeytingLean/Crypto/QKD/BB84/**`

## 1) E91 (Entanglement-Based QKD) — Interface-First, Then Concrete

Status: ✅ implemented (toy CT instantiation) in `HeytingLean/Crypto/QKD/E91/**`.

### 1.1 Interface-first module tree (future DI refinement)

Create:
- `HeytingLean/Crypto/QKD/E91/States.lean`
- `HeytingLean/Crypto/QKD/E91/Tasks.lean`
- `HeytingLean/Crypto/QKD/E91/Security.lean`
- `HeytingLean/Crypto/QKD/E91.lean`

Goal: express E91 as a `TaskCT`-instantiated security statement via the existing theorem:
`superinfo_secure_against_eavesdropping`.

Minimal design:
- Define an E91 substrate `E91Substrate`.
- Provide (or assume via a structure) a `TaskCT.SuperinformationMedium E91Substrate CT`.
- Prove `e91_secure : SecureAgainstEavesdropping E91Substrate CT M` by invoking the generic theorem.

### 1.2 Concrete step (non-vacuous witness)

Replace “assume `SuperinformationMedium`” with a **concrete witness** analogous to BB84:
- Introduce a restricted constructor model where two observables are clonable but not their union.
- Provide a single canonical attack (e.g. “intercept-resend on entangled correlations”) that implies a forbidden copy task.

Deliverables:
- `e91TaskCT : TaskCT E91Substrate`
- `e91Superinfo : SuperinformationMedium E91Substrate e91TaskCT`
- `e91_intercept_impossible` (same pattern as BB84)

## 2) Error-Rate / Detectability Layer (BB84 + E91)

Current BB84 proof is CT-level (“attack requires cloning”). Next is to add an *error-detection semantics* layer without committing to full probability theory.

Status (BB84): ✅ completed (QBER + threshold scaffolding) under `HeytingLean/Crypto/QKD/BB84/ErrorRate/**`.

### 2.1 Interface-first “test” abstraction

Add:
- `HeytingLean/Crypto/QKD/Common/Detectability.lean`

Sketch:
- Define a predicate `Detectable (attack : Task σ) : Prop` and a small interface linking it to tasks/specs, e.g.
  - attacks that disturb incompatible observables are detectable.
- Prove theorems of the form:
  - `attack_requires_cloning_or_detectable : ...`
  - then conclude either impossibility (no-cloning) or detectability.

Important: keep this as an **interface** (structures/typeclasses), not a probabilistic proof, until we decide the exact probability model.

### 2.2 Concrete instantiation later

Potential future targets:
- a finite “toy probability” layer over `Fintype` outcomes;
- or a direct bridge into Mathlib’s probability theory (heavier).

## 3) Multi-Round Security

We already have the “transfer” pattern:
- `composed_security` (if attack implies impossible subtask, attack impossible).

Next is to standardize multi-round composition:

### 3.1 Generic multi-round combinators

Status: ✅ completed via `HeytingLean/Constructor/CT/MultiRound.lean` (syntactic `seqPow`/`parPow` + forward-closure lemmas).

Definitions:
- `parN : Nat → Task σ → Task σ` (iterate `Task.par`)
- `seqN : Nat → Task σ → Task σ` (iterate `Task.seq`)

Lemmas (axiom-free where possible):
- `possible_parN` and `possible_seqN` (from `TaskCT.possible_par/seq`)
- Note: we intentionally **do not** add “projection” lemmas from composite tasks back to components here (CT only gives forward closure in the abstract interface).

### 3.2 BB84 specialization

Status: ✅ completed via `HeytingLean/Crypto/QKD/BB84/MultiRound.lean` (CT-style reduction: multi-round attack ⇒ `copyAll` ⇒ impossible).

Goal:
- `bb84_multi_round_attack_impossible` using `bb84_composed_security`.

## 4) Sanity/QA Targets to Add

- Add `HeytingLean/Tests/Crypto/E91Sanity.lean` once E91 lands.
- Extend the bundle verifier checks list with:
  - `HeytingLean.Crypto.QKD.E91.e91_secure`
  - `HeytingLean.Crypto.QKD.BB84.bb84_multi_round_attack_impossible` (if added)

## Open Questions (Before We Start Coding E91/Detectability)

1. For E91, do we want the *first* concrete witness to be:
   - (A) a BB84-like finite “two incompatible observables” toy model, or
   - (B) a CHSH/Bell-style abstraction (closer to E91’s story)?
2. For detectability, do we want to model:
   - (A) “detection” as a pure `Prop` interface, or
   - (B) a minimal probabilistic bound (requires choosing a probability framework)?

Current answers (2026-01-07):
- E91 witness: (A) first, then (B) later.
- Detectability: (A) first (interface-first), avoid heavy probability imports for now.
