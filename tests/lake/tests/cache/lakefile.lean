import Lake
open System Lake DSL

package test where
  enableArtifactCache := true
  restoreAllArtifacts := get_config? restoreAll |>.isSome

lean_lib Test

lean_lib Module

lean_lib Ignored

lean_exe test where
  root := `Main
