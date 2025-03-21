import Lake
open System Lake DSL

package test

lean_lib lib where
  srcDir := "lib"
  roots := #[`A, `B, `C]

lean_exe a where
  root := `exe

lean_exe b where
  root := `exe

target foo : String :=
  return .pure "foo"
