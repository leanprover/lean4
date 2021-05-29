/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Data.Name
import Lean.Elab.Import
import Leanpkg2.Manifest
import Leanpkg2.Proc

open Lean
open System

namespace Leanpkg2

def buildPath : FilePath := "build"
def tempBuildPath := buildPath / "temp"

structure BuildConfig where
  pkg      : Name
  leanArgs : List String
  leanPath : String
  -- things like `leanpkg.toml` and olean roots of dependencies that should also trigger rebuilds
  moreDeps : List FilePath
