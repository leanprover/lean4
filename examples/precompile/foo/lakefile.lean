import Lake
open Lake DSL

package foo {
  precompileModules := true
}

@[defaultTarget]
lean_lib foo
