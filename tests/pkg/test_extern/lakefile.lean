import Lake
open System Lake DSL

package test_extern where
  precompileModules := true

@[default_target] lean_lib TestExtern
