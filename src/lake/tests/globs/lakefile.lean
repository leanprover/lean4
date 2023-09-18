import Lake

open Lake DSL

package test

@[default_target]
lean_lib TBA where
  globs := #[.andSubmodules `TBA]

@[default_target]
lean_lib Test where
  globs := #[.submodules "Test"]
