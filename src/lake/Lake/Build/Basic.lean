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
  /--
  Fail the top-level build if entries of at least this level have been logged.

  Unlike some build systems, this does **NOT** convert such log entries to
  errors, and it does not abort jobs when warnings are logged (i.e.,
  dependent jobs will still continue unimpeded).
  -/
  failLevel : LogLevel := .error
  /--
  The stream to which Lake reports build progress.
  By default, Lake uses `stderr`.
  -/
  out : OutStream := .stderr
  /-- Whether to use ANSI escape codes in build output. -/
  ansiMode : AnsiMode := .auto

/-- Information on what this job did. -/
inductive JobAction
/-- No information about this job's action is available. -/
| unknown
/-- Tried to load a cached build action (set by `buildFileUnlessUpToDate`) -/
| cache
/-- Tried to fetch a build from a store (can be set by `buildUnlessUpToDate?`) -/
| fetch
/-- Tried to perform a build action (set by `buildUnlessUpToDate?`) -/
| build
deriving Inhabited, Repr, DecidableEq, Ord

instance : LT JobAction := ltOfOrd
instance : LE JobAction := leOfOrd
instance : Min JobAction := minOfLe
instance : Max JobAction := maxOfLe

@[inline] def JobAction.merge (a b : JobAction) : JobAction :=
  max a b

def JobAction.verb (failed : Bool) : JobAction → String
| .unknown => if failed then "Running" else "Ran"
| .cache => if failed then "Revisiting" else "Revisited"
| .fetch => if failed then "Fetching" else "Fetched"
| .build => if failed then "Building" else "Built"

/-- Mutable state of a Lake job. -/
structure JobState where
  /-- The job's log. -/
  log : Log := {}
  /-- Tracks whether this job performed any significant build action. -/
  action : JobAction := .unknown

/--
Resets the job state after a checkpoint (e.g., registering the job).
Preserves state that downstream jobs want to depend on while resetting
job-local state that should not be inherited by downstream jobs.
-/
@[inline] def JobState.renew (_ : JobState) : JobState where
  log := {}
  action := .unknown

def JobState.merge (a b : JobState) : JobState where
  log := a.log ++ b.log
  action := a.action.merge b.action

@[inline] def JobState.modifyLog (f : Log → Log) (s : JobState) :=
  {s with log := f s.log}

/-- The result of a Lake job. -/
abbrev JobResult α := EResult Log.Pos JobState α

/-- The `Task` of a Lake job. -/
abbrev JobTask α := BaseIOTask (JobResult α)

/-- A Lake job. -/
structure Job (α : Type u)  where
  task : JobTask α
  caption : String

/-- A Lake context with a build configuration and additional build data. -/
structure BuildContext extends BuildConfig, Context where
  leanTrace : BuildTrace
  registeredJobs : IO.Ref (Array (Job Unit))

/-- A transformer to equip a monad with a `BuildContext`. -/
abbrev BuildT := ReaderT BuildContext

/-- The monad of asynchronous Lake jobs. Lifts into `FetchM`. -/
abbrev JobM := BuildT <| EStateT Log.Pos JobState BaseIO

instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

instance : MonadStateOf Log JobM where
  get := (·.log) <$> get
  set log := modify fun s => {s with log}
  modifyGet f := modifyGet fun s => let (a, log) := f s.log; (a, {s with log})

instance : MonadStateOf JobState JobM := inferInstance

instance : MonadLog JobM := .ofMonadState
instance : MonadError JobM := ELog.monadError
instance : Alternative JobM := ELog.alternative
instance : MonadLift LogIO JobM := ⟨ELogT.takeAndRun⟩

/-- Record that this job is trying to perform some action. -/
@[inline] def updateAction (action : JobAction) : JobM PUnit :=
  modify fun s => {s with action := s.action.merge action}

/-- A monad equipped with a Lake build context. -/
abbrev MonadBuild (m : Type → Type u) :=
  MonadReaderOf BuildContext m

@[inline] def getBuildContext [MonadBuild m] : m BuildContext :=
  readThe BuildContext

@[inline] def getLeanTrace [Functor m] [MonadBuild m] : m BuildTrace :=
  (·.leanTrace) <$> getBuildContext

@[inline] def getBuildConfig [Functor m] [MonadBuild m] : m BuildConfig :=
  (·.toBuildConfig) <$> getBuildContext

@[inline] def getIsOldMode [Functor m] [MonadBuild m] : m Bool :=
  (·.oldMode) <$> getBuildConfig

@[inline] def getTrustHash [Functor m] [MonadBuild m] : m Bool :=
  (·.trustHash) <$> getBuildConfig

@[inline] def getNoBuild [Functor m] [MonadBuild m] : m Bool :=
  (·.noBuild) <$> getBuildConfig

@[inline] def getVerbosity [Functor m] [MonadBuild m] : m Verbosity :=
  (·.verbosity) <$> getBuildConfig

@[inline] def getIsVerbose [Functor m] [MonadBuild m] : m Bool :=
  (· == .verbose) <$> getVerbosity

@[inline] def getIsQuiet [Functor m] [MonadBuild m] : m Bool :=
  (· == .quiet) <$> getVerbosity

/-- The internal core monad of Lake builds.  Not intended for user use. -/
abbrev CoreBuildM := BuildT LogIO

/-- The monad used to spawn asynchronous Lake build jobs. Lifts into `FetchM`. -/
abbrev SpawnM := BuildT BaseIO

/-- The monad used to spawn asynchronous Lake build jobs. **Replaced by `SpawnM`.** -/
@[deprecated SpawnM] abbrev SchedulerM := SpawnM

/--
Logs a build step with `message`.

**Deprecated:**  Build steps are now managed by a top-level build monitor.
As a result, this no longer functions the way it used to. It now just logs the
`message` via `logVerbose`.
-/
@[deprecated] def logStep (message : String) : JobM Unit := do
  logVerbose message
