/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Monad
import Lake.Build.Context
import Lake.Util.EStateT

open System

namespace Lake

def mkBuildContext (ws : Workspace) (oldMode : Bool) : IO BuildContext := do
  let lean := ws.lakeEnv.lean
  let leanTrace :=
    if lean.githash.isEmpty then
      mixTrace (← computeTrace lean.lean) (← computeTrace lean.sharedLib)
    else
      Hash.ofString lean.githash
  return {opaqueWs := ws, leanTrace, oldMode}

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

/-- Run the given build function in the Workspace's context. -/
@[inline] def Workspace.runBuild (ws : Workspace) (build : BuildM α) (oldMode := false) : LogIO α := do
  let ctx ← mkBuildContext ws oldMode
  build.run ctx

/-- Run the given build function in the Lake monad's workspace. -/
@[inline] def runBuild (build : BuildM α) (oldMode := false) : LakeT LogIO α := do
  (← getWorkspace).runBuild build oldMode
