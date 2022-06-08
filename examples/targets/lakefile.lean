import Lake
open Lake DSL

package targets {
  srcDir := "src"
}

lean_lib foo
lean_lib bar
lean_lib baz

lean_exe a
lean_exe b
lean_exe c
