import Lake
open Lake DSL

package test

@[default_target]
lean_exe foo where
  root := `Main
  srcDir := "foo"

@[default_target]
lean_exe bar where
  root := `Main
  srcDir := "bar"
