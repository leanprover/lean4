import Lake.Package

open Lake System

def package : PackageConfig := {
  name := "foo"
  version := "1.0"
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") },
    { name := "b", src := Source.path (FilePath.mk ".." / "b") }
  ]
}
