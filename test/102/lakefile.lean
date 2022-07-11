import Lake
open Lake DSL

package tba {
  -- add package configuration options here
}

@[defaultTarget]
lean_lib TBA := {
  name := `TBA
  globs := #[.andSubmodules `TBA]
}
