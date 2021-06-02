/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Data.Name
import Lean.Elab.Import
import Leanpkg2.Package
import Leanpkg2.Proc

open Lean
open System

namespace Leanpkg2

structure BuildConfig where
  module   : Name
  leanArgs : List String
  leanPath : String
  -- things like `leanpkg.toml` and olean roots of dependencies that should also trigger rebuilds
  moreDeps : List FilePath

namespace BuildConfig

def fromPackages (module : Name) (leanArgs : List String) (pkgs : List Package) : BuildConfig := {
  module, leanArgs,
  leanPath := SearchPath.toString <| pkgs.map (·.buildDir)
  moreDeps := pkgs.filter (·.dir.toString != ".") |>.map (·.buildRoot.withExtension "olean")
}
