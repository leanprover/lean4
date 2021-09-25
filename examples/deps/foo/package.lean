import Lake
open Lake System

def package : PackageConfig := {
  name := "foo"
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") },
    { name := "b", src := Source.path (FilePath.mk ".." / "b") }
  ]
}
