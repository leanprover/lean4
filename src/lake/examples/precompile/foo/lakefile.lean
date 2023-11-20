import Lake
open Lake DSL

package foo {
  precompileModules := true
}

@[default_target]
lean_lib Foo
