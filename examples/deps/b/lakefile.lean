import Lake
open System Lake DSL

package b {
  dependencies := #[
    { name := `root, src := Source.path (FilePath.mk ".." / "root") }
  ]
}
