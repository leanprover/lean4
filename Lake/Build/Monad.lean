/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Monad
import Lake.Build.Context

open System

namespace Lake

deriving instance Inhabited for BuildContext

def mkBuildContext (ws : Workspace) : IO BuildContext := do
  let lean := ws.lakeEnv.lean
  let leanTrace :=
    if lean.githash.isEmpty then
      mixTrace (← computeTrace lean.lean) (← computeTrace lean.sharedLib)
    else
      Hash.ofString lean.githash
  return {opaqueWs := ws, leanTrace}

@[inline] def getLeanTrace : BuildM BuildTrace :=
  (·.leanTrace) <$> readThe BuildContext

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => pure a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  error s!"build cycle detected:\n{"\n".intercalate cycle}"
