import Lake
open System Lake DSL

package app where
  dependencies := #[{
    name := `ffi
    src := Source.path (FilePath.mk ".." / "lib")
  }]
