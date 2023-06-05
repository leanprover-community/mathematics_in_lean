import Lake
open Lake DSL

package mil {
  -- add package configuration options here
}

@[default_target]
lean_lib MIL {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
