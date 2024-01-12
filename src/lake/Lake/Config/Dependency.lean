/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.NameMap

namespace Lake
open Lean System

/-- The `source` of a `Lake.Dependency`. -/
inductive Source where
/- A package located a fixed path relative to the dependent's directory. -/
| path (dir : FilePath)
/- A package cloned from a Git repository available at a fixed `url`. -/
| git (url : String) (rev : Option String) (subDir : Option FilePath)
/-- A package hosted on GitHub in the repository named `<owner>/<repo>`. -/
| github (owner repo : String) (rev : Option String) (subDir : Option FilePath)
deriving Inhabited, Repr

/-- A `Dependency` of a package. -/
structure Dependency where
  /--
  A `Name` for the dependency.
  The names of a package's dependencies cannot clash.
  -/
  name : Name
  /--
  The source of a dependency.
  See the documentation of `Lake.Source` for supported sources.
  -/
  source  : Source
  /--
  Whether to enable this dependency in the current configuration.
  -/
  enable : Bool
  /--
  Arguments to pass to the dependency's package configuration.
  -/
  opts : NameMap String := {}

deriving Inhabited
