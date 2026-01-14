import Lake
open Lake DSL

package test

lean_lib Hello

@[default_target]
lean_exe hello where
  root := `Main
