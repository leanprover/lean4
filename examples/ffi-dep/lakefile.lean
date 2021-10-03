import Lake
open System Lake DSL

package where
  name := "ffi-dep"
  binName := "add"
  dependencies := #[{
    name := "ffi"
    src := Source.path (FilePath.mk ".." / "ffi")
  }]
