/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
prelude
import Lake.Util.Lock
import Lake.Build.Index
import Lake.Build.Job

/-! # Build Runner

This module defines the top-level functions used to execute a
Lake build, monitor its progress, and await the result.
-/

open System

namespace Lake

/-- Create a fresh build context from a workspace and a build configuration. -/
def mkBuildContext (ws : Workspace) (config : BuildConfig) : BaseIO BuildContext := do
  return {
    opaqueWs := ws,
    toBuildConfig := config,
    registeredJobs := ← IO.mkRef #[],
    leanTrace := .ofHash (pureHash ws.lakeEnv.leanGithash)
      s!"Lean {Lean.versionStringCore}, commit {ws.lakeEnv.leanGithash}"
  }

/-- Unicode icons that make up the spinner in animation order. -/
def Monitor.spinnerFrames :=
  #['⣾','⣷','⣯','⣟','⡿','⢿','⣻','⣽']

/-- Context of the Lake build monitor. -/
structure MonitorContext where
  jobs : IO.Ref (Array OpaqueJob)
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

/-- State of the Lake build monitor. -/
structure MonitorState where
  jobNo : Nat := 0
  totalJobs : Nat := 0
  didBuild : Bool := false
  failures : Array String
  resetCtrl : String
  lastUpdate : Nat
  spinnerIdx : Fin Monitor.spinnerFrames.size := ⟨0, by decide⟩

/-- Monad of the Lake build monitor. -/
abbrev MonitorM := ReaderT MonitorContext <| StateT MonitorState BaseIO

@[inline] def MonitorM.run
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
@[inline] def flush (out : IO.FS.Stream) : BaseIO PUnit :=
  out.flush |>.catchExceptions fun _ => pure ()

/-- Like `IO.FS.Stream.putStr`, but panics on errors. -/
@[inline] def print! (out : IO.FS.Stream) (s : String) : BaseIO PUnit :=
  out.putStr s |>.catchExceptions fun e =>
    panic! s!"[{decl_name%} failed: {e}] {repr s}"

namespace Monitor

@[inline] def print (s : String) : MonitorM PUnit := do
  print! (← read).out s

@[inline] nonrec def flush : MonitorM PUnit := do
  flush (← read).out

def renderProgress (running unfinished : Array OpaqueJob) (h : 0 < unfinished.size) : MonitorM PUnit := do
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



def reportJob (job : OpaqueJob) : MonitorM PUnit := do
  let {jobNo, totalJobs, didBuild, ..} ← get
  let {failLv, outLv, showOptional, out, useAnsi, showProgress, minAction, showTime, ..} ← read
  let {task, caption, optional, ..} := job
  let {log, action, buildTime, ..} := task.get.state
  let maxLv := log.maxLv
  let failed := strictAnd log.hasEntries (maxLv ≥ failLv)
   if !didBuild && action = .build then
    modify fun s => {s with didBuild := true}
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

def poll (unfinished : Array OpaqueJob) : MonitorM (Array OpaqueJob × Array OpaqueJob) := do
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

def sleep : MonitorM PUnit := do
  let now ← IO.monoMsNow
  let lastUpdate := (← get).lastUpdate
  let sleepTime : Nat := (← read).updateFrequency - (now - lastUpdate)
  if sleepTime > 0 then
    IO.sleep sleepTime.toUInt32
  let now ← IO.monoMsNow
  modify fun s => {s with lastUpdate := now}

partial def loop (unfinished : Array OpaqueJob) : MonitorM PUnit := do
  let (running, unfinished) ← poll unfinished
  if h : 0 < unfinished.size then
    renderProgress running unfinished h
    sleep
    loop unfinished

def main (init : Array OpaqueJob) : MonitorM PUnit := do
  loop init
  let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
  unless resetCtrl.isEmpty do
    print resetCtrl
    flush

end Monitor

structure MonitorResult where
  didBuild : Bool
  failures : Array String
  numJobs : Nat

/-- The job monitor function. An auxiliary definition for `runFetchM`. -/
def monitorJobs
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
  let s := {
    resetCtrl
    lastUpdate := ← IO.monoMsNow
    failures := initFailures
  }
  let (_,s) ← Monitor.main initJobs |>.run ctx s
  return {
    failures := s.failures
    numJobs := s.totalJobs
    didBuild := s.didBuild
  }

/-- Save input mappings to the local Lake artifact cache (if enabled). -/
def Workspace.saveInputs (ws : Workspace) : LogIO Unit := do
  unless ws.lakeCache.isDisabled do
    ws.packages.forM fun pkg => do
      if let some ref := pkg.cacheRef? then
        let inputsFile := pkg.inputsFileIn ws.lakeCache
        (← ref.get).save inputsFile

/-- Exit code to return if `--no-build` is set and a build is required. -/
def noBuildCode : ExitCode := 3

/--
Run a build function in the Workspace's context using the provided configuration.
Reports incremental build progress and build logs. In quiet mode, only reports
failing build jobs (e.g., when using `-q` or non-verbose `--no-build`).
-/
def Workspace.runFetchM
  (ws : Workspace) (build : FetchM α) (cfg : BuildConfig := {})
: IO α := do
  -- Configure
  let out ← cfg.out.get
  let useAnsi ← cfg.ansiMode.isEnabled out
  let outLv := cfg.outLv
  let failLv := cfg.failLv
  let isVerbose := cfg.verbosity = .verbose
  let showProgress := cfg.showProgress
  let showSuccess := cfg.showSuccess
  let ctx ← mkBuildContext ws cfg
  -- Job Computation
  let caption := "job computation"
  let compute := Job.async build (caption := caption)
  let job ← compute.run.run'.run ctx |>.run nilTrace
  -- Job Monitor
  let minAction := if isVerbose then .unknown else .fetch
  let showOptional := isVerbose
  let showTime := isVerbose || !useAnsi
  let {failures, numJobs, didBuild} ← monitorJobs #[job] ctx.registeredJobs
    out failLv outLv minAction showOptional useAnsi showProgress showTime
  -- Save input mappings to cache
  match (← ws.saveInputs {}) with
  | .ok _ log =>
    if !log.isEmpty && isVerbose then
      print! out "There were issues saving input mappings to the local artifact cache:\n"
      log.replay (logger := .stream out outLv useAnsi)
  | .error _ log =>
    print! out "Failed to save input mappings to the local artifact cache.\n"
    if isVerbose then
      log.replay (logger := .stream out outLv useAnsi)
  -- Report
  let isNoBuild := cfg.noBuild
  if failures.isEmpty then
    let some a ← job.wait?
      | error "uncaught top-level build failure (this is likely a bug in Lake)"
    if showProgress && showSuccess then
      let jobs := if numJobs == 1 then "1 job" else s!"{numJobs} jobs"
      if isNoBuild then
        print! out s!"All targets up-to-date ({jobs}).\n"
      else
        print! out s!"Build completed successfully ({jobs}).\n"
    return a
  else
    print! out "Some required targets logged failures:\n"
    failures.forM (print! out s!"- {·}\n")
    flush out
    if isNoBuild && didBuild then
      IO.Process.exit noBuildCode.toUInt8
    else
      error "build failed"

/-- Run a build function in the Workspace's context and await the result. -/
@[inline] def Workspace.runBuild
  (ws : Workspace) (build : FetchM (Job α)) (cfg : BuildConfig := {})
: IO α := do
  let job ← ws.runFetchM build cfg
  let some a ← job.wait? | error "build failed"
  return a

/-- Produce a build job in the Lake monad's workspace and await the result. -/
@[inline] def runBuild
  (build : FetchM (Job α)) (cfg : BuildConfig := {})
: LakeT IO α := do
  (← getWorkspace).runBuild build cfg
