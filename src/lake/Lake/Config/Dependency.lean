/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
prelude
import Init.System.FilePath
import Lean.Data.NameMap

/- # Package Dependency Configuration

This module the defines the data types which encode a dependency of a
Lake package (i.e., the information contained in the `require` DSL syntax).
-/

open System Lean

namespace Lake

/--
The source of a `Dependency`.
That is, where Lake should look to materialize the dependency.
-/
inductive DependencySrc where
/- A package located a fixed path relative to the dependent package's directory. -/
| path (dir : FilePath)
/- A package cloned from a Git repository available at a fixed Git `url`. -/
| git (url : String) (rev : Option String) (subDir : Option FilePath)
deriving Inhabited, Repr


/--
A `Dependency` of a package.
It specifies a package which another package depends on.
This encodes the information contained in the `require` DSL syntax.
-/
structure Dependency where
  /--
  The package name of the dependency.
  This name must match the one declared in its configuration file,
  as that name is used to index its target data types. For this reason,
  the package name must also be unique across packages in the dependency graph.
  -/
  name : Name
  /--
  An additional qualifier used to distinguish packages of the same
  name in a Lake registry. On Reservoir, this is the package owner.
  -/
  scope : String
  /--
  The target version of the dependency.
  A Git revision can be specified with the syntax `git#<rev>`.
  -/
  version? : Option String
  /--
  The source of a dependency.
  If none, looks up the dependency in the default registry (e.g., Reservoir).
  See the documentation of `DependencySrc` for supported sources.
  -/
  src?  : Option DependencySrc
  /--
  Arguments to pass to the dependency's package configuration.
  -/
  opts : NameMap String
  deriving Inhabited

/-- The full name of a dependency (i.e., `<scope>/<name>`)-/
def Dependency.fullName (dep : Dependency) : String :=
  s!"{dep.scope}/{dep.name.toString}"
