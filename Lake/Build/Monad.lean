/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package
import Lake.Config.Workspace
import Lake.Build.MonadBasic

open System
open Lean (Name)

namespace Lake

def mkBuildContext (ws : Workspace) (lean : LeanInstall) (lake : LakeInstall) : IO BuildContext := do
  let leanTrace :=
    if lean.githash.isEmpty then
      mixTrace (← computeTrace lean.lean) (← computeTrace lean.sharedLib)
    else
      Hash.ofString lean.githash
  return {workspace := ws, lean, lake, leanTrace}

deriving instance Inhabited for BuildContext

@[inline] def getWorkspace : BuildM Workspace :=
  (·.workspace.get) <$> read

@[inline] def getPackageByName? (name : Name) : BuildM (Option Package) :=
  (·.packageByName? name) <$> getWorkspace

@[inline] def getPackageForModule? (mod : Name) : BuildM (Option Package) :=
  (·.packageForModule? mod) <$> getWorkspace

@[inline] def getOleanPath : BuildM SearchPath :=
  (·.oleanPath) <$> getWorkspace

@[inline] def getLeanInstall : BuildM LeanInstall :=
  (·.lean) <$> read

@[inline] def getLeanOleanDir : BuildM FilePath :=
  (·.oleanDir) <$> getLeanInstall

@[inline] def getLeanIncludeDir : BuildM FilePath :=
  (·.includeDir) <$> getLeanInstall

@[inline] def getLean : BuildM FilePath :=
  (·.lean) <$> getLeanInstall

@[inline] def getLeanTrace : BuildM BuildTrace :=
  (·.leanTrace) <$> read

@[inline] def getLeanc : BuildM FilePath :=
  (·.leanc) <$> getLeanInstall

@[inline] def getLeanAr : BuildM FilePath :=
  (·.ar) <$> getLeanInstall

@[inline] def getLeanCc : BuildM FilePath :=
  (·.cc) <$> getLeanInstall

@[inline] def getLakeInstall : BuildM LakeInstall :=
  (·.lake) <$> read

@[inline] def getLakeOleanDir : BuildM FilePath :=
  (·.oleanDir) <$> getLakeInstall
