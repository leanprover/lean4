/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Task
import Lake.Build.Trace
import Lake.Build.MonadCore
import Lake.Config.InstallPath
import Lake.Config.OpaquePackage

open System
namespace Lake

structure BuildContext where
  leanTrace : BuildTrace
  leanInstall : LeanInstall
  lakeInstall : LakeInstall
  package : OpaquePackage

abbrev BuildM :=
  ReaderT BuildContext BuildCoreM

/-- `Task` type for `BuildM`/`BuildCoreM`. -/
abbrev BuildTask :=
  EIOTask PUnit

def BuildM.run (logMethods : LogMethods BaseIO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  self ctx |>.run logMethods

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  logError s!"build cycle detected:\n{"\n".intercalate cycle}"
  failure
