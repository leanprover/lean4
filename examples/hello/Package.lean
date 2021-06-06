import Leanpkg2.Build

open Leanpkg2

def package : PackageConfig := {
  name := "hello",
  version := "1.0",
}

def configure : IO Unit :=
  Leanpkg2.configure ⟨".", package⟩

def build : IO Unit :=
  Leanpkg2.build ⟨".", package⟩ ["bin"]

def main : IO Unit :=
  build
