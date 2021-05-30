import Leanpkg2.Build
import Leanpkg2.Configure
import Leanpkg2.Manifest

open Leanpkg2

def manifest : Manifest := {
  name := "a",
  version := "1.0",
}

def build : IO Unit :=
  Leanpkg2.build manifest ["lib"]

def main : IO Unit :=
  build
