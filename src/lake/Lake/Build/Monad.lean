/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner, Sebastian Ullrich
-/
import Lake.Config.Monad
import Lake.Build.Context
import Lake.Util.EStateT

open System

namespace Lake

def mkBuildContext (ws : Workspace) (oldMode : Bool) : IO BuildContext := do
  let lean := ws.lakeEnv.lean
  let leanTrace := Hash.ofString lean.githash
  return {
    opaqueWs := ws, leanTrace, oldMode
    startedBuilds := ← IO.mkRef 0
    finishedBuilds := ← IO.mkRef 0
  }

@[inline] def getLeanTrace : BuildM BuildTrace :=
  (·.leanTrace) <$> readThe BuildContext

@[inline] def getIsOldMode : BuildM Bool :=
  (·.oldMode) <$> readThe BuildContext

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => pure a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  error s!"build cycle detected:\n{"\n".intercalate cycle}"

/--
Run the recursive build in the given build store.
If a cycle is encountered, log it and then fail.
-/
@[inline] def RecBuildM.runIn (store : BuildStore) (build : RecBuildM α) : BuildM (α × BuildStore) := do
  let (res, store) ← EStateT.run store <| ReaderT.run build []
  return (← failOnBuildCycle res, store)

/--
Run the recursive build in a fresh build store.
If a cycle is encountered, log it and then fail.
-/
@[inline] def RecBuildM.run (build : RecBuildM α) : BuildM α := do
  (·.1) <$> build.runIn {}

/--
Busy waits to acquire the lock represented by the `lockFile`.
Prints a warning if on the first time it has to wait.
-/
@[inline] partial def busyAcquireLockFile (lockFile : FilePath) : IO PUnit := do
  busyLoop true
where
  busyLoop firstTime :=
    try
      -- Remark: fail if already exists
      -- (not part of POSIX, but supported on all our platforms)
      createParentDirs lockFile
      let h ← IO.FS.Handle.mk lockFile .writeNew
      h.putStrLn <| toString <| ← IO.Process.getPID
    catch
      | .alreadyExists .. => do
        if firstTime then
          let stderr ← IO.getStderr
          stderr.putStrLn s!"warning: waiting for prior `lake build` invocation to finish... (remove '{lockFile}' if stuck)"
          stderr.flush
        IO.sleep (ms := 300)
        busyLoop false
      | e => throw e

/-- Busy wait to acquire the lock of `lockFile`, run `act`, and then release the lock. -/
@[inline] def withLockFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (lockFile : FilePath) (act : m α) : m α := do
  try
    busyAcquireLockFile lockFile; act
  finally show IO _ from do
    try
      IO.FS.removeFile lockFile
    catch
      | .noFileOrDirectory .. => IO.eprintln <|
        s!"warning: `{lockFile}` was deleted before the lock was released"
      | e => throw e

/-- The name of the Lake build lock file name (i.e., `lake.lock`). -/
@[noinline] def lockFileName : String :=
  "lake.lock"

/-- The workspace's build lock file. -/
@[inline] def Workspace.lockFile (self : Workspace) : FilePath :=
  self.root.buildDir / lockFileName

/-- Run the given build function in the Workspace's context. -/
@[inline] def Workspace.runBuild (ws : Workspace) (build : BuildM α) (oldMode := false) : LogIO α := do
  let ctx ← mkBuildContext ws oldMode
  /-
  TODO: 
  The lock file has been temporarily disabled (by lean4#2445)
  until we have an API for catching `Ctrl-C` during a build.
  Absent this, the lock file was too disruptive for users.
  -/
  -- withLockFile ws.lockFile do
  build.run ctx

/-- Run the given build function in the Lake monad's workspace. -/
@[inline] def runBuild (build : BuildM α) (oldMode := false) : LakeT LogIO α := do
  (← getWorkspace).runBuild build oldMode
