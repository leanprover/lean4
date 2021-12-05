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

def mkBuildContext (ws : Workspace) (pkg : Package) (leanInstall : LeanInstall) (lakeInstall : LakeInstall) : IO BuildContext := do
  let leanTrace := mixTrace (← computeTrace leanInstall.lean) (← computeTrace leanInstall.sharedLib)
  return {package := pkg, workspace := ws, leanInstall, lakeInstall, leanTrace}

deriving instance Inhabited for BuildContext

def adaptPackage [MonadWithReaderOf BuildContext m] (pkg : Package) (act : m α) : m α :=
  withReader (fun ctx => {ctx with package := pkg}) act

def getPackage : BuildM Package :=
  (·.package.get) <$> read

def getWorkspace : BuildM Workspace :=
  (·.workspace.get) <$> read

def getPackageByName? (name : Name) : BuildM (Option Package) :=
  (·.packageByName? name) <$> getWorkspace

def getPackageForModule? (mod : Name) : BuildM (Option Package) :=
  (·.packageForModule? mod) <$> getWorkspace

def getBuildDir : BuildM FilePath :=
  (·.buildDir) <$> getPackage

def getOleanPath : BuildM SearchPath :=
  (·.oleanPath) <$> getWorkspace

def getLeanInstall : BuildM LeanInstall :=
  (·.leanInstall) <$> read

def getLeanIncludeDir : BuildM FilePath :=
  (·.includeDir) <$> getLeanInstall

def getLean : BuildM FilePath :=
  (·.lean) <$> getLeanInstall

def getLeanTrace : BuildM BuildTrace := do
  (·.leanTrace) <$> read

def getLeanc : BuildM FilePath :=
  (·.leanc) <$> getLeanInstall

def getLeanAr : BuildM FilePath :=
  (·.ar) <$> getLeanInstall

def getLakeInstall : BuildM LakeInstall :=
  (·.lakeInstall) <$> read
