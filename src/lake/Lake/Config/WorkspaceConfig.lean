/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Defaults
public import Lake.Config.MetaClasses
meta import all Lake.Config.Meta
import Lake.Config.Meta

open System
namespace Lake

/-- A `Workspace`'s declarative configuration. -/
public configuration WorkspaceConfig where
  /--
  The directory to which Lake should download remote dependencies.
  Defaults to `defaultPackagesDir` (i.e., `.lake/packages`).
  -/
  packagesDir : FilePath := defaultPackagesDir
  deriving Inhabited, Repr
