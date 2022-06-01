/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/

namespace Lake
open Lean System

/--
The `src` of a `Dependency`.

In Lake, dependency sources currently come into flavors:
* Local `path`s relative to the package's directory.
* Remote `git` repositories that are download from a given `url`
  into the workspace's `packagesDir`.
-/
inductive Source where
| path (dir : FilePath)
| git (url rev : String)
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
  See the documentation of `Source` for more information.
  -/
  src  : Source
  /--
  The subdirectory of the dependency's source where
  the dependency's package configuration is located.
  -/
  dir  : FilePath := "."
  /--
  Arguments to pass to the dependency's package configuration.
  -/
  args : List String := []

deriving Inhabited, Repr
