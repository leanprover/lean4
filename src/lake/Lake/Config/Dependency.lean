/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Init.Dynamic
public import Init.System.FilePath
public import Init.Data.ToString.Name
public import Lean.Data.NameMap.Basic
public import Lake.Util.Git
public import Lake.Util.Version
import Init.Data.String.TakeDrop

/- # Package Dependency Configuration

This module the defines the data types which encode a dependency of a
Lake package (i.e., the information contained in the `require` DSL syntax).
-/

open System Lean

namespace Lake

/-- A version targeted by a dependency (e.g., in a `require`). -/
public inductive InputVer
/-- No version was specified. -/
| protected none
/--
A Git revision to resolve to a commit hash.

This is specified by an  `@ git <rev>`  clause in Lean or `rev = <rev>` field in TOML.
-/
| protected git (rev : GitRev)
/--
A semantic version range of acceptable versions.

This is specified by an `@ <ver>` clause in Lean or `verison = <ver>` field in TOML.
-/
| protected ver (ver : VerRange)
deriving Inhabited, Repr

namespace InputVer

public def parse (ver : String) : Except String InputVer :=
  if let some ver := ver.dropPrefix? "git#" then
    return .git ver.toString
  else
    match VerRange.parse ver with
    | .ok ver => return .ver ver
    | .error e => throw e

public def toString? (self : InputVer) : Option String :=
  match self with
  | .none => none
  | .git rev => some s!"git#{rev}"
  | .ver ver => some ver.toString

end InputVer

/--
The source of a `Dependency`.
That is, where Lake should look to materialize the dependency.
-/
public inductive DependencySrc where
/- A package located at a fixed path relative to the dependent package's directory. -/
| path (dir : FilePath)
/- A package cloned from a Git repository available at a fixed Git `url`. -/
| git (url : String) (rev : Option String) (subDir : Option FilePath)
deriving Inhabited, Repr

/--
A `Dependency` of a package.
It specifies a package which another package depends on.
This encodes the information contained in the `require` DSL syntax.
-/
public structure Dependency where
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
  -/
  version : InputVer
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
  deriving Inhabited, TypeName

namespace Dependency

/-- Returns the directory name used for storing the materialized depedency. -/
@[inline] public def dirName (dep : Dependency) : String :=
  dep.name.toString (escape := false)

/-- Returns the name of the dependency formatted for printing. -/
@[inline] public def prettyName (dep : Dependency) : String :=
  dep.name.toString (escape := false)

/-- Returns the name of the dependency formatted for lookup on Reservoir. -/
@[inline] public def reservoirName (dep : Dependency) : String :=
  dep.name.toString (escape := false)

/-- Returns the full name of the dependency  (i.e., `<scope>/<name>`) formatted for printing. -/
@[inline] public def fullName (dep : Dependency) : String :=
  s!"{dep.scope}/{dep.prettyName}"

/--  Returns a printable string which uniquely identifies this dependency for the resolver. -/
@[inline] public def resolverDescr (dep : Dependency) : String :=
  let name :=  dep.name.toString (escape := false)
  let name := dep.version.toString?.elim name (s!"{name}@{·}")
  if dep.scope.isEmpty then name else s!"{dep.scope}/{name}"
