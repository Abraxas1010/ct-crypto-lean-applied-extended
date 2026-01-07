import Lake
open Lake DSL

package «CTCrypto» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib «HeytingLean» where
  -- Root of the Lean source tree
  roots := #[`HeytingLean]
