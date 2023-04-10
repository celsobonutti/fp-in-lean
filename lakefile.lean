import Lake
open Lake DSL

package «fp-in-lean» {
  -- add package configuration options here
}

lean_lib «FpInLean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fp-in-lean» {
  root := `Main
}
