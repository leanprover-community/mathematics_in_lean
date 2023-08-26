import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  -- this is set in mathlib, but the exercises are nicer to read without it
  -- "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

package mil where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib MIL where
  moreLeanArgs := moreLeanArgs

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
