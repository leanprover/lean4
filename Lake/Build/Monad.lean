/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package
import Lake.Build.MonadBasic

open System
namespace Lake

def mkBuildContext (pkg : Package) (leanInstall : LeanInstall) (lakeInstall : LakeInstall) : IO BuildContext := do
  let leanTrace := mixTrace (← computeTrace leanInstall.lean) (← computeTrace leanInstall.sharedLib)
  return {package := pkg, leanInstall, lakeInstall, leanTrace}

deriving instance Inhabited for BuildContext

def BuildM.adaptPackage (pkg : Package) (self : BuildM α) : BuildM α :=
  self.adapt fun r => {r with package := pkg}

export BuildM (adaptPackage)

def getPackage : BuildM Package :=
  (·.package.get) <$> read

def getWorkspace : BuildM Workspace :=
  (·.workspace) <$> getPackage

def getBuildDir : BuildM FilePath :=
  (·.buildDir) <$> getPackage

def getOleanDir : BuildM FilePath :=
  (·.oleanDir) <$> getPackage

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
