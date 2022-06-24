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

def mkBuildContext (ws : Workspace) (lean : LeanInstall) (lake : LakeInstall) : IO BuildContext := do
  let leanTrace :=
    if lean.githash.isEmpty then
      mixTrace (← computeTrace lean.lean) (← computeTrace lean.sharedLib)
    else
      Hash.ofString lean.githash
  return {opaqueWs := ws, lean, lake, leanTrace}

instance [Monad m] : MonadLake (BuildT m) where
  getLeanInstall := (·.lean) <$> read
  getLakeInstall := (·.lake) <$> read
  getWorkspace := (·.workspace) <$> read

@[inline] def getLeanTrace : BuildM BuildTrace :=
  (·.leanTrace) <$> read

def failOnBuildCycle [ToString k] : Except (List k) α → BuildM α
| Except.ok a => pure a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  error s!"build cycle detected:\n{"\n".intercalate cycle}"
