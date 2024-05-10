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

/-- The job monitor function. An auxiliary definition for `runFetchM`. -/
partial def monitorJobs
  (jobs : Array (String × Job Unit))
  (out : IO.FS.Stream)
  (failLv outLv : LogLevel)
  (showANSIProgress : Bool)
  (resetCtrl : String := "")
  (initFailures : Array String := #[])
  (totalJobs := jobs.size)
  (updateMs := 100)
: IO (Array String) := do
  loop jobs resetCtrl (← IO.monoMsNow) initFailures
where
  loop jobs resetCtrl lastUpdate initFailures := do
    let mut unfinishedJobs := #[]
    let mut failures := initFailures
    let mut resetCtrl := resetCtrl
    for jobEntry@(caption, job) in jobs do
      if (← IO.hasFinished job.task) then
        let log := job.task.get.state
        let failed := log.hasEntriesGe failLv
        if failed then
          failures := failures.push caption
        if log.hasEntriesGe outLv then
          let jobsDone := totalJobs - jobs.size + unfinishedJobs.size + 1
          out.putStr s!"{resetCtrl}[{jobsDone}/{totalJobs}] {caption}\n"
          resetCtrl := ""
          let outLv := if failed then .trace else outLv
          log.replay (logger := MonadLog.stream out outLv)
          out.flush
      else
        unfinishedJobs := unfinishedJobs.push jobEntry
    if h : 0 < unfinishedJobs.size then
      if showANSIProgress then
        let jobsDone := totalJobs - jobs.size
        let (caption, _) := unfinishedJobs[0]'h
        out.putStr s!"{resetCtrl}[{jobsDone}/{totalJobs}] {caption}"
        resetCtrl := "\x1B[2K\r"
        out.flush
      let now ← IO.monoMsNow
      let sleepTime : Nat := updateMs - (now - lastUpdate)
      if sleepTime > 0 then
        IO.sleep sleepTime.toUInt32
      loop unfinishedJobs resetCtrl now failures
    else
      unless resetCtrl.isEmpty do
        out.putStr resetCtrl
      return failures

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
  let out ← if cfg.useStdout then IO.getStdout else IO.getStderr
  let useANSI ← out.isTty
  let verbosity := cfg.verbosity
  let outLv := verbosity.minLogLevel
  let failLv : LogLevel := if ctx.failIfWarnings then .warning else .error
  let showProgress :=
    (cfg.noBuild ∧ verbosity == .verbose) ∨
    verbosity != .quiet
  let showANSIProgress := showProgress ∧ useANSI
  -- Job Computation
  let caption := "Computing build jobs"
  let header := s!"[?/?] {caption}"
  if showANSIProgress then
    out.putStr header
    out.flush
  let (a?, log) ← ((withLoggedIO build).run.run'.run ctx).captureLog
  let failed := log.hasEntriesGe failLv
  if log.hasEntriesGe outLv then
    unless showANSIProgress do
      out.putStr header
      out.putStr "\n"
    let outLv := if failed then .trace else outLv
    log.replay (logger := MonadLog.stream out outLv)
    out.flush
  let failures := if failed then #[caption] else #[]
  -- Job Monitor
  let jobs ← ctx.registeredJobs.get
  let resetCtrl := if showANSIProgress then "\x1B[2K\r" else ""
  let failures ← monitorJobs jobs out failLv outLv showANSIProgress
    (resetCtrl := resetCtrl) (initFailures := failures)
  -- Failure Report
  if failures.isEmpty then
    let some a := a?
      | error "top-level build failed"
    if showProgress then
      out.putStr s!"All builds jobs completed successfully.\n"
    return a
  else
    out.putStr "Some build steps logged failures:\n"
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
