import Lake
open Lake DSL

package "unicode" where
  -- add package configuration options here

@[default_target]
lean_exe "unicode" where
  root := `Main
