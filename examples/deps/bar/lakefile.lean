import Lake
open System Lake DSL

package where
  name := "bar"
  dependencies := [
    { name := "foo", src := Source.path (FilePath.mk ".." /  "foo") }
  ]
  binRoot := `Main
