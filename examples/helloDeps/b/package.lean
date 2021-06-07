import Lake.Build

open Lake System

def package : PackageConfig := {
  name := "b"
  version := "1.0"
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") }
  ]
}
