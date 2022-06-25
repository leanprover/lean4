import Lake
open System Lake DSL

package app

require ffi from ".."/"lib"

@[defaultTarget]
lean_exe app {
  root := `Main
}

lean_lib Test
