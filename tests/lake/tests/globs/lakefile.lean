import Lake

open Lake DSL

package test

lean_lib TBA where
  globs := `TBA.*

lean_lib Test where
  globs := #[`Test.+]
