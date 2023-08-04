/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Task
import Lake.Util.Error
import Lake.Util.OptionIO
import Lake.Config.Context
import Lake.Build.Trace
import Lake.Build.Store
import Lake.Build.Topological

open System
namespace Lake

/-- A Lake context with some additional caching for builds. -/
structure BuildContext extends Context where
  leanTrace : BuildTrace
  oldMode : Bool := false
  startedBuilds : IO.Ref Nat
  finishedBuilds : IO.Ref Nat

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

/-- The monad for the Lake build manager. -/
abbrev SchedulerM := BuildT <| LogT BaseIO

/-- The core monad for Lake builds. -/
abbrev BuildM := BuildT LogIO

/-- A transformer to equip a monad with a Lake build store. -/
abbrev BuildStoreT := StateT BuildStore

/-- A Lake build cycle. -/
abbrev BuildCycle := Cycle BuildKey

/-- A transformer for monads that may encounter a build cycle. -/
abbrev BuildCycleT := CycleT BuildKey

/-- A recursive build of a Lake build store that may encounter a cycle. -/
abbrev RecBuildM := BuildCycleT <| BuildStoreT BuildM

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

@[inline] def BuildM.run (ctx : BuildContext) (self : BuildM α) : LogIO α :=
  self ctx

def BuildM.catchFailure (f : Unit → BaseIO α) (self : BuildM α) : SchedulerM α :=
  fun ctx logMethods => self ctx logMethods |>.catchFailure f

def logStep (message : String) : BuildM Unit := do
  let done ← (← read).finishedBuilds.get
  let started ← (← read).startedBuilds.get
  logInfo s!"[{done}/{started}] {message}"

def createParentDirs (path : FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
