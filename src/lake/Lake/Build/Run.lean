/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
module

prelude
public import Lake.Config.Workspace
import Lake.Config.Monad
import Lake.Build.Job.Monad
import Lake.Build.Index
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

/-! # Build Runner

This module defines the top-level functions used to execute a
Lake build, monitor its progress, and await the result.
-/

open System

namespace Lake

/-- Create a fresh build context from a workspace and a build configuration. -/
@[deprecated "Deprecated without replacement." (since := "2025-01-08")]
public def mkBuildContext (ws : Workspace) (config : BuildConfig) : BaseIO BuildContext := do
  return {
    opaqueWs := ws,
    toBuildConfig := config,
    registeredJobs := ← IO.mkRef #[],
    leanTrace := .ofHash (pureHash ws.lakeEnv.leanGithash)
      s!"Lean {Lean.versionStringCore}, commit {ws.lakeEnv.leanGithash}"
  }

/-- Unicode icons that make up the spinner in animation order. -/
private def Monitor.spinnerFrames :=
  #['⣾','⣷','⣯','⣟','⡿','⢿','⣻','⣽']

/-- Context of the Lake build monitor. -/
private structure MonitorContext where
  jobs : JobQueue
  out : IO.FS.Stream
  outLv : LogLevel
  failLv : LogLevel
  minAction : JobAction
  showOptional : Bool
  useAnsi : Bool
  showProgress : Bool
  showTime : Bool
  /-- How often to poll jobs (in milliseconds). -/
  updateFrequency : Nat

@[inline] def MonitorContext.logger (ctx : MonitorContext) : MonadLog BaseIO :=
  .stream ctx.out ctx.outLv ctx.useAnsi

/-- State of the Lake build monitor. -/
private structure MonitorState where
  jobNo : Nat := 0
  totalJobs : Nat := 0
  wantsRebuild : Bool := false
  failures : Array String
  resetCtrl : String
  lastUpdate : Nat
  spinnerIdx : Fin Monitor.spinnerFrames.size := ⟨0, by decide⟩

/-- Monad of the Lake build monitor. -/
private abbrev MonitorM := ReaderT MonitorContext <| StateT MonitorState BaseIO

@[inline] private def MonitorM.run
  (ctx : MonitorContext) (s : MonitorState) (self : MonitorM α)
: BaseIO (α × MonitorState) :=
  self ctx s

/--
The ANSI escape sequence for clearing the current line
and resetting the cursor back to the start.
-/
def Ansi.resetLine : String :=
  "\x1B[2K\r"

/-- Like `IO.FS.Stream.flush`, but ignores errors. -/
@[inline] private def flush (out : IO.FS.Stream) : BaseIO PUnit :=
  out.flush |>.catchExceptions fun _ => pure ()

/-- Like `IO.FS.Stream.putStr`, but panics on errors. -/
@[inline] private def print! (out : IO.FS.Stream) (s : String) : BaseIO PUnit :=
  out.putStr s |>.catchExceptions fun e =>
    panic! s!"[{decl_name%} failed: {e}] {repr s}"

namespace Monitor

@[inline] private def print (s : String) : MonitorM PUnit := do
  print! (← read).out s

@[inline] private nonrec def flush : MonitorM PUnit := do
  flush (← read).out

private def renderProgress (running unfinished : Array OpaqueJob) (h : 0 < unfinished.size) : MonitorM PUnit := do
  let {jobNo, totalJobs, ..} ← get
  let {useAnsi, showProgress, ..} ← read
  if showProgress ∧ useAnsi then
    let spinnerIcon ← modifyGet fun s =>
        (spinnerFrames[s.spinnerIdx], {s with spinnerIdx := s.spinnerIdx + ⟨1, by decide⟩})
    let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := Ansi.resetLine})
    let caption :=
      -- Prefer the newest running job.
      -- This avoids the monitor focusing too long on any one job.
      -- (e.g., "Running job computation")
      if _ : 0 < running.size then
        s!"Running {running[running.size - 1].caption} (+ {running.size - 1} more)"
      else
        s!"Running {unfinished[unfinished.size - 1].caption}"
    print s!"{resetCtrl}{spinnerIcon} [{jobNo}/{totalJobs}] {caption}"
    flush

private def reportJob (job : OpaqueJob) : MonitorM PUnit := do
  let {jobNo, totalJobs, ..} ← get
  let {failLv, outLv, showOptional, out, useAnsi, showProgress, minAction, showTime, ..} ← read
  let {task, caption, optional, ..} := job
  let {log, action, wantsRebuild, buildTime, ..} := task.get.state
  let maxLv := log.maxLv
  let failed := strictAnd log.hasEntries (maxLv ≥ failLv)
  if wantsRebuild then
    modify fun s => if s.wantsRebuild then s else {s with wantsRebuild := true}
  if failed && !optional then
    modify fun s => {s with failures := s.failures.push caption}
  let hasOutput := failed || (log.hasEntries && maxLv ≥ outLv)
  let showJob :=
    (!optional || showOptional) &&
    (hasOutput || (showProgress && !useAnsi && action ≥ minAction))
  if showJob then
    let verb := action.verb failed
    let icon := if hasOutput then maxLv.icon else '✔'
    let opt := if optional then " (Optional)" else ""
    let time := if showTime && buildTime > 0 then s!" ({formatTime buildTime})" else ""
    let caption := s!"{icon} [{jobNo}/{totalJobs}]{opt} {verb} {caption}{time}"
    let caption :=
      if useAnsi then
        let color := if hasOutput then maxLv.ansiColor else "32"
        Ansi.chalk color caption
      else
        caption
    let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
    print s!"{resetCtrl}{caption}\n"
    if hasOutput then
      let outLv := if failed then .trace else outLv
      log.replay (logger := .stream out outLv useAnsi)
    flush
where
  formatTime ms :=
    if ms > 10000 then s!"{ms / 1000}s"
    else if ms > 1000 then s!"{(ms) / 1000}.{(ms+50) / 100 % 10}s"
    else s!"{ms}ms"

private def poll (unfinished : Array OpaqueJob) : MonitorM (Array OpaqueJob × Array OpaqueJob) := do
  let newJobs ← (← read).jobs.modifyGet ((·, #[]))
  modify fun s => {s with totalJobs := s.totalJobs + newJobs.size}
  let pollJobs := fun (running, unfinished) job => do
    match (← IO.getTaskState job.task) with
    | .finished =>
      reportJob job
      modify fun s => {s with jobNo := s.jobNo + 1}
      return (running, unfinished)
    | .running =>
      return (running.push job, unfinished.push job)
    | .waiting =>
      return (running, unfinished.push job)
  let r ← unfinished.foldlM pollJobs (#[], #[])
  newJobs.foldlM pollJobs r

private def sleep : MonitorM PUnit := do
  let now ← IO.monoMsNow
  let lastUpdate := (← get).lastUpdate
  let sleepTime : Nat := (← read).updateFrequency - (now - lastUpdate)
  if sleepTime > 0 then
    IO.sleep sleepTime.toUInt32
  let now ← IO.monoMsNow
  modify fun s => {s with lastUpdate := now}

private  partial def loop (unfinished : Array OpaqueJob) : MonitorM PUnit := do
  let (running, unfinished) ← poll unfinished
  if h : 0 < unfinished.size then
    renderProgress running unfinished h
    sleep
    loop unfinished

private def main (init : Array OpaqueJob) : MonitorM PUnit := do
  loop init
  let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
  unless resetCtrl.isEmpty do
    print resetCtrl
    flush

end Monitor

/-- **For internal use only.** -/
public structure MonitorResult where
  wantsRebuild : Bool
  failures : Array String
  numJobs : Nat

@[inline] def MonitorResult.isOk (self : MonitorResult) : Bool :=
  self.failures.isEmpty

def mkMonitorContext (cfg : BuildConfig) (jobs : JobQueue) : BaseIO MonitorContext := do
  let out ← cfg.out.get
  let useAnsi ← cfg.ansiMode.isEnabled out
  let outLv := cfg.outLv
  let failLv := cfg.failLv
  let isVerbose := cfg.verbosity = .verbose
  let showProgress := cfg.showProgress
  let minAction := if isVerbose then .unknown else .fetch
  let showOptional := isVerbose
  let showTime := isVerbose || !useAnsi
  let updateFrequency := 100
  return {
    jobs, out, failLv, outLv, minAction, showOptional
    useAnsi, showProgress, showTime, updateFrequency
  }

def monitorJobs'
  (ctx : MonitorContext)
  (initJobs : Array OpaqueJob)
  (initFailures : Array String := #[])
  (resetCtrl : String := "")
: BaseIO MonitorResult := do
  let s := {
    resetCtrl
    lastUpdate := ← IO.monoMsNow
    failures := initFailures
  }
  let (_,s) ← Monitor.main initJobs |>.run ctx s
  return {
    failures := s.failures
    numJobs := s.totalJobs
    wantsRebuild := s.wantsRebuild
  }

/-- The job monitor function. An auxiliary definition for `runFetchM`. -/
@[inline, deprecated "Deprecated without replacement." (since := "2025-01-08")]
public def monitorJobs
  (initJobs : Array OpaqueJob)
  (jobs : IO.Ref (Array OpaqueJob))
  (out : IO.FS.Stream)
  (failLv outLv : LogLevel)
  (minAction : JobAction)
  (showOptional useAnsi showProgress showTime : Bool)
  (resetCtrl : String := "")
  (initFailures : Array String := #[])
  (updateFrequency := 100)
: BaseIO MonitorResult := do
  let ctx := {
    jobs, out, failLv, outLv, minAction, showOptional
    useAnsi, showProgress, showTime, updateFrequency
  }
  monitorJobs' ctx initJobs initFailures resetCtrl

/-- Exit code to return if `--no-build` is set and a build is required. -/
public def noBuildCode : ExitCode := 3

def Workspace.saveOutputs
  [logger : MonadLog BaseIO] (ws : Workspace)
  (out : IO.FS.Stream) (outputsFile : FilePath) (isVerbose : Bool)
: BaseIO Unit := do
  unless ws.isRootArtifactCacheEnabled do
    logWarning s!"{ws.root.prettyName}: \
      the artifact cache is not enabled for this package, so the artifacts described \
      by the mappings produced by `-o` will not necessarily be available in the cache."
  if let some ref := ws.root.outputsRef? then
    match (← (← ref.get).writeFile outputsFile {}) with
    | .ok _ log =>
      if !log.isEmpty && isVerbose then
        print! out "There were issues saving input-to-output mappings from the build:\n"
        log.replay
    | .error _ log =>
      print! out "Failed to save input-to-output mappings from the build.\n"
      if isVerbose then
        log.replay
  else
    print! out "Workspace missing input-to-output mappings from build. (This is likely a bug in Lake.)\n"

def reportResult (cfg : BuildConfig) (out : IO.FS.Stream) (result : MonitorResult) : BaseIO Unit := do
  if result.failures.isEmpty then
    if cfg.showProgress && cfg.showSuccess then
      let numJobs := result.numJobs
      let jobs := if numJobs == 1 then "1 job" else s!"{numJobs} jobs"
      if cfg.noBuild then
        print! out s!"All targets up-to-date ({jobs}).\n"
      else
        print! out s!"Build completed successfully ({jobs}).\n"
  else
    print! out "Some required targets logged failures:\n"
    result.failures.forM (print! out s!"- {·}\n")
    flush out

structure BuildResult (α : Type u) extends MonitorResult where
  out : Except String α

instance : CoeOut (BuildResult α) MonitorResult := ⟨BuildResult.toMonitorResult⟩

@[inline] def BuildResult.isOk (self : BuildResult α) : Bool :=
  self.out.isOk

def monitorJob (ctx : MonitorContext) (job : Job α) : BaseIO (BuildResult α) := do
  let result ← monitorJobs' ctx #[job]
  if result.isOk then
    if let some a ← job.wait? then
      return {toMonitorResult := result, out := .ok a}
    else
      -- Computation job failed but was unreported in the monitor. This should be impossible.
      return {toMonitorResult := result, out := .error <|
        "uncaught top-level build failure (this is likely a bug in Lake)"}
  else
    return {toMonitorResult := result, out := .error "build failed"}

def mkBuildContext' (ws : Workspace) (cfg : BuildConfig) (jobs : JobQueue) : BuildContext where
  opaqueWs := ws
  toBuildConfig := cfg
  registeredJobs := jobs
  leanTrace := .ofHash (pureHash ws.lakeEnv.leanGithash)
    s!"Lean {Lean.versionStringCore}, commit {ws.lakeEnv.leanGithash}"

def Workspace.startBuild
  (ws : Workspace)  (cfg : BuildConfig) (jobs : JobQueue) (build : FetchM α)
  (caption := "job computation")
: BaseIO (Job α) := do
  let bctx := mkBuildContext' ws cfg jobs
  let compute := Job.async build (caption := caption)
  compute.run.run'.run bctx |>.run nilTrace

def Workspace.finalizeBuild
  (ws : Workspace) (cfg : BuildConfig) (ctx : MonitorContext) (result : BuildResult α)
: IO α := do
  reportResult cfg ctx.out result
  if let some outputsFile := cfg.outputsFile? then
    ws.saveOutputs (logger := ctx.logger) ctx.out outputsFile (cfg.verbosity matches .verbose)
  match result.out with
  | .ok a =>
    return a
  | .error e =>
    if cfg.noBuild && result.wantsRebuild then
      IO.Process.exit noBuildCode.toUInt8
    else
      throw (IO.userError e)

/--
Run a build function in the Workspace's context using the provided configuration.
Reports incremental build progress and build logs. In quiet mode, only reports
failing build jobs (e.g., when using `-q` or non-verbose `--no-build`).
-/
public def Workspace.runFetchM
  (ws : Workspace) (build : FetchM α) (cfg : BuildConfig := {}) (caption := "job computation")
: IO α := do
  let jobs ← mkJobQueue
  let mctx ← mkMonitorContext cfg jobs
  let job ← ws.startBuild cfg jobs build caption
  let result ← monitorJob mctx job
  ws.finalizeBuild cfg mctx result

def monitorBuild (mctx : MonitorContext) (job : Job (Job α)) : BaseIO (BuildResult α) := do
  let result ← monitorJob mctx job
  match result.out with
  | .ok job =>
    if let some a ← job.wait? then
      return {result with out := .ok a}
    else
      -- Job failed but was unreported in the monitor. It was likely not properly registered.
      return {result with out := .error <|
        "uncaught top-level build failure (this is likely a bug in the build script)"}
  | .error e =>
    return {result with out := .error e}

/--
Returns whether a build is needed to validate `build`. Does not report on the attempted build.

This is equivalent to checking whether `lake build --no-build` exits with code 0.
-/
public def Workspace.checkNoBuild
  (ws : Workspace) (build : FetchM (Job α))
: BaseIO Bool := do
  let jobs ← mkJobQueue
  let cfg := {noBuild := true}
  let mctx ← mkMonitorContext cfg jobs
  let job ← ws.startBuild cfg jobs build
  let result ← monitorBuild mctx job
  return result.isOk -- `isOk` means no failures, and thus no `--no-build` failures

/-- Run a build function in the Workspace's context and await the result. -/
public def Workspace.runBuild
  (ws : Workspace) (build : FetchM (Job α)) (cfg : BuildConfig := {})
: IO α := do
  let jobs ← mkJobQueue
  let mctx ← mkMonitorContext cfg jobs
  let job ← ws.startBuild cfg jobs build
  let result ← monitorBuild mctx job
  ws.finalizeBuild cfg mctx result

/-- Produce a build job in the Lake monad's workspace and await the result. -/
@[inline] public def runBuild
  (build : FetchM (Job α)) (cfg : BuildConfig := {})
: LakeT IO α := do (← getWorkspace).runBuild build cfg
