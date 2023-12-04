import Lake
open Lake DSL

package mil where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib MIL where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

