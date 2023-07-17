import Lake
open Lake DSL

package tba {
  -- add package configuration options here
}

@[default_target]
lean_lib TBA := {
  name := `TBA
  globs := #[.andSubmodules `TBA]
}
