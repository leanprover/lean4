/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open System
namespace Lake

/-- The default setting for a `WorkspaceConfig`'s `packagesDir` option. -/
def defaultPackagesDir : FilePath := "lean_packages"

/-- A `Workspace`'s declarative configuration. -/
structure WorkspaceConfig where
  /--
  The directory to which Lake should download remote dependencies.
  Defaults to `defaultPackagesDir` (i.e., `lean_packages`).
  -/
  packagesDir : FilePath := defaultPackagesDir
  deriving Inhabited, Repr
