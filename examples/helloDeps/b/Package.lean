import Leanpkg2.Build

open Leanpkg2 System

def package : PackageConfig := {
  name := "b",
  version := "1.0",
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") }
  ]
}

def build : IO Unit := do
  Leanpkg2.build ⟨".", package⟩ ["bin", "LINK_OPTS=../a/build/lib/libA.a"]

def main : IO Unit :=
  build
