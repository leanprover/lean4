import Lake
open System Lake DSL

package bar where
  dependencies := #[
    { name := `foo, src := Source.path (FilePath.mk ".." / "foo") }
  ]
