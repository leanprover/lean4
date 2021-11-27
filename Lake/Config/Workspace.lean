/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

open System
namespace Lake

/-- The default setting for a `WorkspaceConfig`'s `depsDir` option. -/
def defaultDepsDir : FilePath := "lean_packages"

/-- A `Workspace`'s declarative configuration. -/
structure WorkspaceConfig where
  /--
  The directory to which Lake should download dependencies.
  Defaults to `defaultDepsDir` (i.e., `lean_packages`).
  -/
  depsDir : FilePath := defaultDepsDir
  deriving Inhabited, Repr

/-- A Lake workspace -- the top-level package directory. -/
structure Workspace where
  /-- The path to the workspace's directory. -/
  dir : FilePath
  /-- The workspace's configuration. -/
  config : WorkspaceConfig
  deriving Inhabited, Repr

namespace Workspace

/-- The workspace's `dir` joined with its `depsDir` configuration. -/
def depsDir (self : Workspace) : FilePath :=
  self.dir / self.config.depsDir
