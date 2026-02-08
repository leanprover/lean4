import Lake
open System Lake DSL

package test

require dep from "dep"

lean_lib lib where
  srcDir := "lib"
  roots := #[`A, `B, `C]

lean_exe a where
  root := `exe

lean_exe b where
  root := `exe

target foo : String := Job.sync do
  return "foo"
