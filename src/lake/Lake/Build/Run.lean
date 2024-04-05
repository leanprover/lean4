/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
import Lake.Util.Lock
import Lake.Build.Index

open System

namespace Lake

/-- Create a fresh build context from a workspace and a build configuration. -/
def mkBuildContext (ws : Workspace) (config : BuildConfig) : BaseIO BuildContext := do
  return {
    opaqueWs := ws,
    toBuildConfig := config,
    buildJobs := ← IO.mkRef #[],
    leanTrace := Hash.ofString ws.lakeEnv.leanGithash
  }

/-- Run a recursive build. -/
@[inline] def RecBuildM.run
  (stack : CallStack BuildKey) (store : BuildStore) (build : RecBuildM α)
: CoreBuildM (α × BuildStore) := do
  build stack store

/-- Run a recursive build in a fresh build store. -/
@[inline] def RecBuildM.run' (build : RecBuildM α) : CoreBuildM α := do
  (·.1) <$> build.run {} {}

/--
Run the given recursive build using the Lake build index
and a topological / suspending scheduler.
-/
def IndexBuildM.run (build : IndexBuildM α) : RecBuildM α :=
  build (inline <| recFetchMemoize BuildInfo.key recBuildWithIndex)

def monitorBuildJobs
  (ctx : BuildContext) (out : IO.FS.Stream) (spawner : CoreBuildM α)
: IO (Option α) := do
  print "[?/?] Computing build jobs"
  let (io, a?, log) ← IO.FS.withIsolatedStreams (spawner.run ctx).captureLog
  if io.isEmpty && log.isEmpty then
    resetLine
  else
    print "\n"
    unless log.isEmpty do
      log.replay (logger := MonadLog.stream out ctx.verbosity)
    unless io.isEmpty do
      out.putStr "stdout/stderr:\n"
      out.putStr io
  let jobs ← ctx.buildJobs.get
  let numJobs := jobs.size
  numJobs.forM fun i => do
    let (caption, job) := jobs[i]!
    print s!"[{i+1}/{numJobs}] {caption}"
    let log := (← IO.wait job.task).state
    if log.isEmpty then
      resetLine
    else
      print "\n"
      log.replay (logger := MonadLog.stream out ctx.verbosity)
  return a?
where
  print s := out.putStr s
  resetLine := print "\n" --"\x1B[2K\r"

/-- The name of the Lake build lock file name (i.e., `lake.lock`). -/
def lockFileName : String :=
  "lake.lock"

/-- The workspace's build lock file. -/
@[inline] def Workspace.lockFile (self : Workspace) : FilePath :=
  self.root.buildDir / lockFileName

/-- Run a build function in the Workspace's context. -/
def Workspace.runBuildM
  (ws : Workspace) (build : IndexBuildM α)
  (cfg : BuildConfig := {}) (useStdout := false)
: IO (Option α) := do
  let ctx ← mkBuildContext ws cfg
  /-
  TODO:
  The lock file has been temporarily disabled (by lean4#2445)
  until we have an API for catching `Ctrl-C` during a build.
  Absent this, the lock file was too disruptive for users.
  -/
  -- withLockFile ws.lockFile do
  let out ← if useStdout then IO.getStdout else IO.getStderr
  inline <| monitorBuildJobs ctx out build.run.run'

/-- Run a build function in the Workspace's context and await the result. -/
@[inline] def Workspace.runBuild
  (ws : Workspace) (build : IndexBuildM (BuildJob α))
  (cfg : BuildConfig := {}) (useStdout := false)
: LogIO α := do
  let some job ← ws.runBuildM build cfg useStdout | error "build failed"
  let some a ← job.await? | error "build failed"
  return a

/-- Produce a build job in the  Lake monad's workspace and await the result. -/
@[inline] def runBuild
  (build : IndexBuildM (BuildJob α))
  (cfg : BuildConfig := {}) (useStdout := false)
: LakeT LogIO α := do
  (← getWorkspace).runBuild build cfg useStdout
