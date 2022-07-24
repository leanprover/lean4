import Lake
open Lake DSL

package hello

lean_lib Hello

@[defaultTarget]
lean_exe hello {
  root := `Main
}
