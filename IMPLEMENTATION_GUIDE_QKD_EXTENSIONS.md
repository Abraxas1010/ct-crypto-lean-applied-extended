# QKD Extensions Implementation Guide (CT‑Crypto Bundle)

This guide specifies the **implemented**, `sorry`‑free extensions to the BB84 formalization
inside `WIP/CT_Crypto_Repo/RESEARCHER_BUNDLE/HeytingLean/`.

Design constraints (enforced by `RESEARCHER_BUNDLE/scripts/verify_ct_crypto.sh`):
- `sorry`/`admit`: **0**
- strict builds: `lake build --wfail`
- no new global axioms (use *parameters/structures* if assumptions are needed)
- interface‑first: prefer lightweight models over heavy probability/quantum semantics

## Status (as of 2026‑01‑07)

| Extension | Status | Entry points |
|----------:|:------:|--------------|
| 1) E91 | ✅ (toy CT instantiation) | `HeytingLean/Crypto/QKD/E91.lean`, `HeytingLean/Tests/Crypto/E91Sanity.lean` |
| 1b) E91 (DI / CHSH) | ✅ | `HeytingLean/Crypto/QKD/E91/DI.lean`, `HeytingLean/Tests/Crypto/E91DISanity.lean` |
| 2) Error rate / QBER | ✅ | `HeytingLean/Crypto/QKD/BB84/ErrorRate.lean`, `HeytingLean/Tests/Crypto/BB84ErrorRateSanity.lean` |
| 3) Multi‑round (composable, CT‑style) | ✅ | `HeytingLean/Constructor/CT/MultiRound.lean`, `HeytingLean/Crypto/QKD/BB84/MultiRound.lean`, `HeytingLean/Tests/Crypto/BB84MultiRoundSanity.lean` |

---

# Extension 1: E91 (Entanglement‑Based QKD)

## 1.1 What’s implemented (toy, CT‑native)

We provide a **non‑trivial TaskCT instantiation** for an E91‑like protocol shape without
formalizing CHSH/Tsirelson yet.

The implemented idea is the same pattern as BB84:
- two incompatible “contexts” (`key` vs `test`) are individually clonable,
- their union is **not** clonable (superinformation),
- therefore eavesdropping tasks requiring cloning are impossible.

This is the *correct* dependency direction for the codebase today:
it lets crypto proofs depend on CT interfaces now, while the device‑independent CHSH layer
can be added later as a refinement.

## 1.2 File structure (implemented)

```
HeytingLean/Crypto/QKD/E91/
  States.lean        -- `Context` + finite state space `E91State`
  Tasks.lean         -- `copyKey`, `copyTest`, `copyAll`
  Constructors.lean  -- `e91TaskCT` + `copyAll_impossible`
  Superinfo.lean     -- `e91Superinfo : SuperinformationMedium`
  Eavesdropping.lean -- `interceptStrategy` (requires `copyAll`)
  Security.lean      -- `e91_secure`, `intercept_impossible`
HeytingLean/Crypto/QKD/E91.lean
HeytingLean/Tests/Crypto/E91Sanity.lean
```

## 1.3 Key theorems (implemented)

- `HeytingLean.Crypto.QKD.E91.copyAll_impossible`
- `HeytingLean.Crypto.QKD.E91.e91_secure`
- `HeytingLean.Crypto.QKD.E91.intercept_impossible`

## 1.4 Future refinement (not implemented here)

Device‑independent E91 via CHSH/Tsirelson is implemented as a separate slice:
- `HeytingLean/Crypto/QKD/E91/DI/**`
- `HeytingLean/Tests/Crypto/E91DISanity.lean`

If you extend it further:
- keep it **separate** from the CT‑core interface (new folder `HeytingLean/Crypto/QKD/E91/DI/**`);
- avoid global axioms: package bounds/assumptions as structure fields;
- prove bridges from “CHSH violation model” → “requires cloning (or other impossible task)”.

---

# Extension 2: Error‑Rate Analysis (BB84 QBER)

## 2.1 What’s implemented (interface‑first)

We avoid importing a heavy probability framework. Instead we:
- define QBER over finite samples (`KeyComparison.qberReal`);
- define an intercept‑resend interception rate `p` and show expected QBER is `p/4`;
- add a conservative 11% threshold predicate;
- record a Hoeffding‑style bound as a function and prove basic algebraic facts about it.

## 2.2 File structure (implemented)

```
HeytingLean/Crypto/QKD/BB84/ErrorRate/
  QBER.lean
  InterceptResend.lean
  Threshold.lean
  Detection.lean
HeytingLean/Crypto/QKD/BB84/ErrorRate.lean
HeytingLean/Tests/Crypto/BB84ErrorRateSanity.lean
```

## 2.3 Key theorems (implemented)

- `HeytingLean.Crypto.QKD.BB84.ErrorRate.expectedQBER_eq_rate_div_4`
- `HeytingLean.Crypto.QKD.BB84.ErrorRate.full_interception_detected`
- `HeytingLean.Crypto.QKD.BB84.ErrorRate.interception_detectable`
- `HeytingLean.Crypto.QKD.BB84.ErrorRate.secure_implies_limited_interception`

---

# Extension 3: Multi‑Round / “Composable” Security (CT‑style)

## 3.1 What’s implemented (and why)

The CT‑core interface provides **forward closure** only:
`possible T` and `possible U` imply `possible (T;U)` / `possible (T ⊗ U)`.

So the implemented “multi‑round” layer is:
- syntactic repetition combinators (`seqPow` / `parPow`);
- possibility‑lifting lemmas (forward direction only);
- reduction theorems for BB84: if an `n`‑round attack implies the forbidden subtask
  `copyAll`, then that `n`‑round attack is impossible.

This matches the project’s reduction‑based security story and stays `sorry`‑free.

## 3.2 File structure (implemented)

```
HeytingLean/Constructor/CT/MultiRound.lean
HeytingLean/Crypto/QKD/BB84/MultiRound.lean
HeytingLean/Tests/Crypto/BB84MultiRoundSanity.lean
```

## 3.3 Key theorems (implemented)

- `HeytingLean.Constructor.CT.Task.seqPow`
- `HeytingLean.Constructor.CT.Task.parPow`
- `HeytingLean.Constructor.CT.TaskCT.possible_seqPow_succ`
- `HeytingLean.Constructor.CT.TaskCT.possible_parPow_succ`
- `HeytingLean.Crypto.QKD.BB84.bb84_attackSeqPow_impossible`
- `HeytingLean.Crypto.QKD.BB84.bb84_attackParPow_impossible`

## 3.4 Future refinement (not implemented here)

An entropy‑based “privacy amplification + leftover hash lemma” development is a
separate research track. If/when you add it:
- keep it in a new folder (e.g. `HeytingLean/Crypto/QKD/Composable/**`);
- start with **interfaces** and small finite witnesses; avoid global axioms;
- only introduce probability theory after deciding the exact model and tradeoffs.

---

# Verification (Bundle)

From `WIP/CT_Crypto_Repo/RESEARCHER_BUNDLE/`:

```bash
./scripts/verify_ct_crypto.sh
```

This runs:
- strict library build (`lake build --wfail`)
- sanity checks via umbrella `HeytingLean.lean`
- key theorem `#check` validations
- axiom printouts for selected theorems
