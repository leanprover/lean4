import Lake
open System Lake DSL

package where
  name := "foo"
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") },
    { name := "b", src := Source.path (FilePath.mk ".." / "b") }
  ]
