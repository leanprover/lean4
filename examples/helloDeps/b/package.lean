import Leanpkg2.Build

open Leanpkg2 System

def package : PackageConfig := {
  name := "b"
  version := "1.0"
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") }
  ]
}
