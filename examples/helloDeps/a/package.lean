import Leanpkg2.Build

open Leanpkg2

def package : PackageConfig := {
  name := "a",
  version := "1.0",
}

def build : IO Unit :=
  Leanpkg2.build ⟨".", package⟩ ["lib"]

def main : IO Unit :=
  build
