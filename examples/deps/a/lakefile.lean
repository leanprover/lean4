import Lake
open System Lake DSL

package a {
  dependencies := #[
    { name := `root, src := Source.path (FilePath.mk ".." / "root") }
  ]
}
