import Lake
open Lake DSL

package «fp-in-lean» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «FpInLean» {
  -- add library configuration options here
}

lean_lib «Anu» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fp-in-lean» {
  root := `Main
}
