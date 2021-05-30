import Leanpkg2.Build
import Leanpkg2.Manifest

open Leanpkg2

def manifest : Manifest := {
  name := "hello",
  version := "1.0",
}

def configure : IO Unit :=
  Leanpkg2.configure manifest

def build : IO Unit :=
  Leanpkg2.build manifest ["bin"]

def main : IO Unit :=
  build
