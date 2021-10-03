import Lake
open System Lake DSL

package ffi_dep where
  binName := "add"
  dependencies := #[{
    name := `ffi
    src := Source.path (FilePath.mk ".." / "ffi")
  }]
