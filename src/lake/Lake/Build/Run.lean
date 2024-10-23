/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
import Lake.Util.Lock
import Lake.Build.Index

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
    leanTrace := Hash.ofString ws.lakeEnv.leanGithash
  }

/-- Unicode icons that make up the spinner in animation order. -/
def Monitor.spinnerFrames :=
  #['⣾','⣷','⣯','⣟','⡿','⢿','⣻','⣽']

/-- Context of the Lake build monitor. -/
structure MonitorContext where
  totalJobs : Nat
  out : IO.FS.Stream
  outLv : LogLevel
  failLv : LogLevel
  minAction : JobAction
  showOptional : Bool
  useAnsi : Bool
  showProgress : Bool
  /-- How often to poll jobs (in milliseconds). -/
  updateFrequency : Nat

/-- State of the Lake build monitor. -/
structure MonitorState where
  jobNo : Nat := 1
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
  let {jobNo, ..} ← get
  let {totalJobs, useAnsi, showProgress, ..} ← read
  if showProgress ∧ useAnsi then
    let spinnerIcon ← modifyGet fun s =>
        (spinnerFrames[s.spinnerIdx], {s with spinnerIdx := s.spinnerIdx + ⟨1, by decide⟩})
    let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := Ansi.resetLine})
    let caption :=
      if _ : 0 < running.size then
        s!"Running {running[0].caption} (+ {running.size - 1} more)"
      else
        s!"Running {unfinished[0].caption}"
    print s!"{resetCtrl}{spinnerIcon} [{jobNo}/{totalJobs}] {caption}"
    flush

def reportJob (job : OpaqueJob) : MonitorM PUnit := do
  let {jobNo, ..} ← get
  let {totalJobs, failLv, outLv, showOptional, out, useAnsi, showProgress, minAction, ..} ← read
  let {task, caption, optional} := job.toJob
  let {log, action, ..} := task.get.state
  let maxLv := log.maxLv
  let failed := log.hasEntries ∧ maxLv ≥ failLv
  if failed ∧ ¬optional then
    modify fun s => {s with failures := s.failures.push caption}
  let hasOutput := failed ∨ (log.hasEntries ∧ maxLv ≥ outLv)
  let showJob :=
    (¬ optional ∨ showOptional) ∧
    (hasOutput ∨ (showProgress ∧ ¬ useAnsi ∧ action ≥ minAction))
  if showJob then
    let verb := action.verb failed
    let icon := if hasOutput then maxLv.icon else '✔'
    let opt := if optional then " (Optional)" else ""
    let caption := s!"{icon} [{jobNo}/{totalJobs}]{opt} {verb} {caption}"
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

def poll (jobs : Array OpaqueJob): MonitorM (Array OpaqueJob × Array OpaqueJob) := do
  jobs.foldlM (init := (#[], #[])) fun (running, unfinished) job => do
    match (← IO.getTaskState job.task) with
    | .finished =>
      reportJob job
      modify fun s => {s with jobNo := s.jobNo + 1}
      return (running, unfinished)
    | .running =>
      return (running.push job, unfinished.push job)
    | .waiting =>
      return (running, unfinished.push job)

def sleep : MonitorM PUnit := do
  let now ← IO.monoMsNow
  let lastUpdate := (← get).lastUpdate
  let sleepTime : Nat := (← read).updateFrequency - (now - lastUpdate)
  if sleepTime > 0 then
    IO.sleep sleepTime.toUInt32
  let now ← IO.monoMsNow
  modify fun s => {s with lastUpdate := now}

partial def loop (jobs : Array OpaqueJob) : MonitorM PUnit := do
  let (running, unfinished) ← poll jobs
  if h : 0 < unfinished.size then
    renderProgress running unfinished h
    sleep
    loop unfinished

def main (jobs : Array OpaqueJob) : MonitorM PUnit := do
  loop jobs
  let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
  unless resetCtrl.isEmpty do
    print resetCtrl
    flush

end Monitor

/-- The job monitor function. An auxiliary definition for `runFetchM`. -/
def monitorJobs
  (jobs : Array OpaqueJob)
  (out : IO.FS.Stream)
  (failLv outLv : LogLevel)
  (minAction : JobAction)
  (showOptional useAnsi showProgress : Bool)
  (resetCtrl : String := "")
  (initFailures : Array String := #[])
  (totalJobs := jobs.size)
  (updateFrequency := 100)
: BaseIO (Array String) := do
  let ctx := {
    totalJobs, out, failLv, outLv, minAction, showOptional
    useAnsi, showProgress, updateFrequency
  }
  let s := {
    resetCtrl
    lastUpdate := ← IO.monoMsNow
    failures := initFailures
  }
  let (_,s) ← Monitor.main jobs |>.run ctx s
  return s.failures

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
  let showProgress := cfg.showProgress
  let showAnsiProgress := showProgress ∧ useAnsi
  let ctx ← mkBuildContext ws cfg
  -- Job Computation
  let caption := "Computing build jobs"
  if showAnsiProgress then
    print! out s!"⣿ [?/?] {caption}"
    flush out
  let (a?, log) ← ((withLoggedIO build).run.run'.run ctx).run?
  let failed := log.hasEntries ∧ log.maxLv ≥ failLv
  if failed ∨ (log.hasEntries ∧ log.maxLv ≥ outLv) then
    let icon := log.maxLv.icon
    let caption := s!"{icon} [?/?] {caption}"
    if useAnsi then
      let caption := Ansi.chalk log.maxLv.ansiColor caption
      if showProgress then
        print! out s!"{Ansi.resetLine}{caption}"
      else
        print! out caption
    else
      print! out caption
    print! out "\n"
    let outLv := if failed then .trace else outLv
    log.replay (logger := .stream out outLv useAnsi)
    flush out
  let failures := if failed then #[caption] else #[]
  -- Job Monitor
  let jobs ← ctx.registeredJobs.get
  let resetCtrl := if showAnsiProgress then Ansi.resetLine else ""
  let minAction := if cfg.verbosity = .verbose then .unknown else .fetch
  let showOptional := cfg.verbosity = .verbose
  let failures ← monitorJobs jobs out failLv outLv minAction showOptional useAnsi showProgress
    (resetCtrl := resetCtrl) (initFailures := failures)
  -- Failure Report
  if failures.isEmpty then
    let some a := a?
      | error "top-level build failed"
    return a
  else
    print! out "Some required builds logged failures:\n"
    failures.forM (print! out s!"- {·}\n")
    flush out
    error "build failed"

/-- Run a build function in the Workspace's context and await the result. -/
@[inline] def Workspace.runBuild
  (ws : Workspace) (build : FetchM (BuildJob α)) (cfg : BuildConfig := {})
: IO α := do
  let job ← ws.runFetchM build cfg
  let some a ← job.wait? | error "build failed"
  return a

/-- Produce a build job in the Lake monad's workspace and await the result. -/
@[inline] def runBuild
  (build : FetchM (BuildJob α)) (cfg : BuildConfig := {})
: LakeT IO α := do
  (← getWorkspace).runBuild build cfg
