/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Log
import Lake.Util.Exit
import Lake.Util.Task
import Lake.Util.Lift
import Lake.Config.Context
import Lake.Build.Trace

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
  verbosity : Verbosity := .normal

abbrev JobResult α := EResult Nat Log α
abbrev JobTask α := BaseIOTask (JobResult α)

/-- A Lake job. -/
structure Job (α : Type u)  where
  task : JobTask α

/-- A Lake context with a build configuration and additional build data. -/
structure BuildContext extends BuildConfig, Context where
  leanTrace : BuildTrace
  buildJobs : IO.Ref (Array (String × Job Unit))

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

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

/-- The internal core monad of Lake builds.  Not intended for user use. -/
abbrev CoreBuildM := BuildT LogIO

/-- The monad of asynchronous Lake jobs. -/
abbrev JobM := CoreBuildM

/-- The monad used to spawn asynchronous Lake build jobs. Lifts into `FetchM`. -/
abbrev SpawnM := BuildT BaseIO

/-- The monad used to spawn asynchronous Lake build jobs. **Replaced by `SpawnM`.** -/
@[deprecated SpawnM] abbrev SchedulerM := SpawnM
