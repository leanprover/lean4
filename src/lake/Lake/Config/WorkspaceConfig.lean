/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open System
namespace Lake

/--
The default directory to output Lake-related files
(e.g., build artifacts, packages, caches, etc.).
Currently not configurable.
-/
def defaultLakeDir : FilePath := ".lake"

/-- The default setting for a `WorkspaceConfig`'s `packagesDir` option. -/
def defaultPackagesDir : FilePath := "packages"

/-- A `Workspace`'s declarative configuration. -/
structure WorkspaceConfig where
  /--
  The directory to which Lake should download remote dependencies.
  Defaults to `defaultLakeDir / defaultPackagesDir` (i.e., `.lake/packages`).
  -/
  packagesDir : FilePath := defaultLakeDir / defaultPackagesDir
  deriving Inhabited, Repr
