import Lake
open Lake DSL

package hello

lean_lib Hello

@[default_target]
lean_exe hello {
  root := `Main
}
