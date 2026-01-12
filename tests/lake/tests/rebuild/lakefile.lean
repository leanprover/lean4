import Lake
open Lake DSL

package foo

lean_lib Foo

@[default_target]
lean_exe foo where
  root := `Main
