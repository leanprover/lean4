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

/-- State of the Lake build monitor. -/
structure MonitorState where
  jobs : Array (Job Unit)
  failures : Array String
  resetCtrl : String
  lastUpdate : Nat

/-- The job monitor function. An auxiliary definition for `runFetchM`. -/
partial def monitorJobs
  (jobs : Array (Job Unit))
  (out : IO.FS.Stream)
  (failLv outLv : LogLevel)
  (useAnsi showProgress : Bool)
  (resetCtrl : String := "")
  (initFailures : Array String := #[])
  (totalJobs := jobs.size)
  (updateMs := 100)
: IO (Array String) := do
  let (_,s) ← StateT.run loop {
      jobs, resetCtrl
      lastUpdate := ← IO.monoMsNow
      failures := initFailures
  }
  return s.failures
where
  loop : StateT MonitorState IO PUnit := do
    let jobs ← modifyGet fun s => (s.jobs, {s with jobs := #[]})
    for h : i in [0:jobs.size] do
      let job := jobs[i]'h.upper
      if (← IO.hasFinished job.task) then
        let {log, action, ..} := (← job.wait).state
        let maxLv := log.maxLogLevel
        let failed := !log.isEmpty ∧ maxLv ≥ failLv
        if failed then
          modify fun s => {s with failures := s.failures.push job.caption}
        let hasOutput := !log.isEmpty ∧ maxLv ≥ outLv
        if hasOutput ∨ (showProgress ∧ action == .build) then
          let verb := action.verb failed
          let icon := if hasOutput then maxLv.icon else '✔'
          let jobNo := (totalJobs - jobs.size) + (i - (← get).jobs.size) + 1
          let caption := s!"{icon} [{jobNo}/{totalJobs}] {verb} {job.caption}"
          let caption :=
            if useAnsi then
              let color := if hasOutput then maxLv.ansiColor else "32"
              Ansi.chalk color caption
            else
              caption
          let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := ""})
          out.putStr s!"{resetCtrl}{caption}\n"
          if hasOutput then
            let outLv := if failed then .trace else outLv
            log.replay (logger := .stream out outLv useAnsi)
          out.flush
      else
        modify fun s => {s with jobs := s.jobs.push job}
    let jobs := (← get).jobs
    if h : 0 < jobs.size then
      if showProgress ∧ useAnsi then
        let jobsDone := totalJobs - jobs.size
        let caption := jobs[0]'h |>.caption
        let resetCtrl ← modifyGet fun s => (s.resetCtrl, {s with resetCtrl := "\x1B[2K\r"})
        out.putStr s!"{resetCtrl}[{jobsDone}/{totalJobs}] Checking {caption}"
        out.flush
      let now ← IO.monoMsNow
      let lastUpdate ← modifyGet fun s => (s.lastUpdate, {s with lastUpdate := now})
      let sleepTime : Nat := updateMs - (now - lastUpdate)
      if sleepTime > 0 then
        IO.sleep sleepTime.toUInt32
      loop
    else unless resetCtrl.isEmpty do
      out.putStr resetCtrl

/--
Whether the build should show progress information.

`Verbosity.quiet` hides progress and, for a `noBuild`,
`Verbosity.verbose` shows progress.
-/
def BuildConfig.showProgress (cfg : BuildConfig) : Bool :=
  (cfg.noBuild ∧ cfg.verbosity == .verbose) ∨ cfg.verbosity != .quiet

/--
Run a build function in the Workspace's context using the provided configuration.
Reports incremental build progress and build logs. In quiet mode, only reports
failing build jobs (e.g., when using `-q` or non-verbose `--no-build`).
-/
def Workspace.runFetchM
  (ws : Workspace) (build : FetchM α) (cfg : BuildConfig := {})
: IO α := do
  -- Configure
  let ctx ← mkBuildContext ws cfg
  let out ← cfg.out.get
  let useAnsi ← cfg.ansiMode.isEnabled out
  let outLv := cfg.verbosity.minLogLevel
  let failLv := cfg.failLevel
  let showProgress := cfg.showProgress
  let showAnsiProgress := showProgress ∧ useAnsi
  -- Job Computation
  let caption := "Computing build jobs"
  let header := s!"[?/?] {caption}"
  if showAnsiProgress then
    out.putStr header
    out.flush
  let (a?, log) ← ((withLoggedIO build).run.run'.run ctx).captureLog
  let failed := log.hasEntriesGe failLv
  if log.hasEntriesGe outLv then
    unless showAnsiProgress do
      out.putStr header
    out.putStr "\n"
    let outLv := if failed then .trace else outLv
    log.replay (logger := .stream out outLv useAnsi)
    out.flush
  let failures := if failed then #[caption] else #[]
  -- Job Monitor
  let jobs ← ctx.registeredJobs.get
  let resetCtrl := if showAnsiProgress then "\x1B[2K\r" else ""
  let failures ← monitorJobs jobs out failLv outLv useAnsi showProgress
    (resetCtrl := resetCtrl) (initFailures := failures)
  -- Failure Report
  if failures.isEmpty then
    let some a := a?
      | error "top-level build failed"
    if showProgress then
      out.putStr s!"Build completed successfully.\n"
    return a
  else
    out.putStr "Some builds logged failures:\n"
    failures.forM (out.putStr s!"- {·}\n")
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
