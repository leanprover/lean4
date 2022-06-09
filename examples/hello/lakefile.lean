import Lake
open Lake DSL

package hello

@[defaultTarget]
lean_exe hello {
  root := `Main
}
