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

/--
Run a build function in the Workspace's context using the provided configuration.
Reports incremental build progress and build logs. In quiet mode, only reports
failing build jobs (e.g., when using `-q` or non-verbose `--no-build`).
-/
def Workspace.runFetchM
  (ws : Workspace) (build : FetchM α) (cfg : BuildConfig := {})
: IO α := do
  let ctx ← mkBuildContext ws cfg
  let out ← if cfg.useStdout then IO.getStdout else IO.getStderr
  let useANSI ← out.isTty
  let verbosity := cfg.verbosity
  let showProgress :=
    (cfg.noBuild && verbosity == .verbose) ||
    verbosity != .quiet
  let caption := "Computing build jobs"
  let header := s!"[?/?] {caption}"
  if showProgress then
    out.putStr header; out.flush
  let (io, a?, log) ← IO.FS.withIsolatedStreams (build.run.run'.run ctx).captureLog
  if io.isEmpty && !log.hasVisibleEntries verbosity then
    if useANSI then out.putStr "\x1B[2K\r" else out.putStr "\n"
  else
    unless showProgress do
      out.putStr header
    out.putStr "\n"
    if log.hasVisibleEntries verbosity then
      log.replay (logger := MonadLog.stream out verbosity)
    unless io.isEmpty do
      out.putStr "stdout/stderr:\n"
      out.putStr io
    out.flush
  let failLv : LogLevel := if ctx.failIfWarnings then .warning else .error
  let failures := if log.any (·.level ≥ failLv) then #[caption] else #[]
  let jobs ← ctx.registeredJobs.get
  let numJobs := jobs.size
  let failures ← numJobs.foldM (init := failures) fun i s => Prod.snd <$> StateT.run (s := s) do
    let (caption, job) := jobs[i]!
    let header := s!"[{i+1}/{numJobs}] {caption}"
    if showProgress then
      out.putStr header; out.flush
    let log := (← job.wait).state
    if log.any (·.level ≥ failLv) then
      modify (·.push caption)
    if !log.hasVisibleEntries verbosity then
      if useANSI then out.putStr "\x1B[2K\r" else out.putStr "\n"
    else
      unless showProgress do
        out.putStr header
      out.putStr "\n"
      log.replay (logger := MonadLog.stream out verbosity)
      out.flush
  if failures.isEmpty then
    let some a := a?
      | error "build failed"
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
