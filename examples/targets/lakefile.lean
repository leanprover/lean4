import Lake
open Lake DSL

package targets {
  srcDir := "src"
}

@[defaultTarget]
lean_lib foo
lean_lib bar
lean_lib baz

lean_exe a
lean_exe b

@[defaultTarget]
lean_exe c
