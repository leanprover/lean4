/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Task
import Lake.Config.Opaque
import Lake.Config.InstallPath
import Lake.Build.Trace
import Lake.Build.IO

open System
namespace Lake

structure BuildContext where
  workspace : OpaqueWorkspace
  leanInstall : LeanInstall
  lakeInstall : LakeInstall
  leanTrace : BuildTrace

abbrev BuildM :=
  ReaderT BuildContext BuildIO

/-- `Task` type for `BuildM`/`BuildIO`. -/
abbrev BuildTask :=
  OptionIOTask

def BuildM.run (logMethods : LogMethods BaseIO) (ctx : BuildContext) (self : BuildM α) : IO α :=
  self ctx |>.run logMethods

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  error s!"build cycle detected:\n{"\n".intercalate cycle}"
