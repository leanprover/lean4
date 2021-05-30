import Leanpkg2.Build
import Leanpkg2.Manifest

open Leanpkg2 System

def manifest : Manifest := {
  name := "b",
  version := "1.0",
  dependencies := [
    { name := "a", src := Source.path (FilePath.mk ".." / "a") }
  ]
}

def build : IO Unit := do
  Leanpkg2.build manifest ["bin", "LINK_OPTS=../a/build/lib/libA.a"]

def main : IO Unit :=
  build
