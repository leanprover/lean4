import Lake
open System Lake DSL

package app

require ffi from ".."/"lib"

@[default_target]
lean_exe app where
  root := `Main

lean_lib Test where
  precompileModules := true
