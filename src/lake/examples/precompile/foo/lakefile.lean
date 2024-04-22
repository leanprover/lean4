import Lake
open Lake DSL

package foo where
  precompileModules := true

@[default_target]
lean_lib Foo
