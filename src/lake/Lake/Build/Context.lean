/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Exit
import Lake.Util.Task
import Lake.Util.Error
import Lake.Util.OptionIO
import Lake.Config.Context
import Lake.Build.Trace
import Lake.Build.Store
import Lake.Build.Topological

open System
namespace Lake

/-- Exit code to return if `--no-build` is set and a build is required. -/
def noBuildCode : ExitCode := 3

/-- Configuration options for a Lake build. -/
structure BuildConfig where
  oldMode : Bool := false
  trustHash : Bool := true
  /-- Early exit if a target has to be rebuilt. -/
  noBuild : Bool := false

/-- A Lake context with a build configuration and additional build data. -/
structure BuildContext extends BuildConfig, Context where
  leanTrace : BuildTrace
  startedBuilds : IO.Ref Nat
  finishedBuilds : IO.Ref Nat

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

@[inline] def getLeanTrace [Monad m] : BuildT m BuildTrace :=
  (·.leanTrace) <$> readThe BuildContext

@[inline] def getBuildConfig [Monad m] : BuildT m BuildConfig :=
  (·.toBuildConfig) <$> readThe BuildContext

@[inline] def getIsOldMode [Monad m] : BuildT m Bool :=
  (·.oldMode) <$> getBuildConfig

@[inline] def getTrustHash [Monad m] : BuildT m Bool :=
  (·.trustHash) <$> getBuildConfig

@[inline] def getNoBuild [Monad m] : BuildT m Bool :=
  (·.noBuild) <$> getBuildConfig

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
