/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.NameMap

namespace Lake
open Lean System

/--
The source of a  `Lake.PackageDepConfig`.
That is, where Lake should look to materialize the dependency.
-/
inductive PackageDepSrc where
/- A package located a fixed path relative to the dependent's directory. -/
| path (dir : FilePath)
/- A package cloned from a Git repository available at a fixed `url`. -/
| git (url : String) (rev? : Option String) (subDir? : Option FilePath)
/-- A package hosted on GitHub in the repository named `<owner>/<repo>`. -/
| github (owner repo : String) (rev? : Option String) (subDir? : Option FilePath)
deriving Inhabited, Repr

/--
Specifies what package another package depends on.
This encodes the information contained in the `require` DSL syntax.
-/
structure PackageDepConfig where
  /--
  The package name of the dependency.
  This name must match the one declared in its configuration file,
  as that name is used to index its target data types. For this reason,
  the package name must also be unique across packages in the dependency graph.
  -/
  name : Name
  /--
  The full name of the package used to lookup the dependency in a registry.
  -/
  fullName : String
  /--
  The target version of the dependency.
  This can be an exact commit or a more general specifier (e.g., a branch).
  -/
  version? : Option String
  /--
  The source of a dependency.
  If none, looks up the dependency in the default registry (e.g., Reservoir).
  See the documentation of `Lake.PackageDepSrc` for supported sources.
  -/
  source?  : Option PackageDepSrc
  /--
  Whether the dependency was declared with a condition (e.g., an `if` clause).
  -/
  conditional : Bool
  /--
  Whether to enable this dependency in the current configuration.
  That is, whether the dependency's `if` clause evaluated to true.
  -/
  enable : Bool
  /--
  Arguments to pass to the dependency's package configuration.
  -/
  options : NameMap String := {}

deriving Inhabited
