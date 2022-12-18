/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Context
import Lake.Config.Workspace

open System
open Lean (Name)

namespace Lake

abbrev MonadLakeEnv (m : Type → Type u) :=
  MonadReaderOf Lake.Env m

abbrev MonadWorkspace (m : Type → Type u) :=
  MonadReaderOf Workspace m

abbrev MonadLake (m : Type → Type u) :=
  MonadReaderOf Context m

/-- Make a `Lake.Context` from a `Workspace`. -/
def mkLakeContext (ws : Workspace) : Context where
  opaqueWs := ws

@[inline] def Context.workspace (self : Context) :=
  self.opaqueWs.get

instance [MonadLake m] [Functor m] : MonadWorkspace m where
  read := (·.workspace) <$> read

section
variable [MonadWorkspace m] [Functor m]

instance : MonadLakeEnv m where
  read := (·.lakeEnv) <$> read

/-! ## Workspace Helpers -/

@[inline] def getWorkspace : m Workspace :=
  read

@[inline] def findPackage? (name : Name) : m (Option Package) :=
  (·.findPackage? name) <$> getWorkspace

@[inline] def findModule? (mod : Name) : m (Option Module) :=
  (·.findModule? mod) <$> getWorkspace

@[inline] def findLeanExe? (mod : Name) : m (Option LeanExe) :=
  (·.findLeanExe? mod) <$> getWorkspace

@[inline] def findLeanLib? (mod : Name) : m (Option LeanLib) :=
  (·.findLeanLib? mod) <$> getWorkspace

@[inline] def findExternLib? (mod : Name) : m (Option ExternLib) :=
  (·.findExternLib? mod) <$> getWorkspace

/-- Get the `leanPath` of the `Workspace`. -/
@[inline] def getLeanPath : m SearchPath :=
  (·.leanPath) <$> getWorkspace

/-- Get the `leanSrcPath` of the `Workspace`. -/
@[inline] def getLeanSrcPath : m SearchPath :=
  (·.leanSrcPath) <$> getWorkspace

/-- Get the `libPath` value of the `Workspace`. -/
@[inline] def getLibPath : m SearchPath :=
  (·.libPath) <$> getWorkspace

/-- Get the `augmentedLeanPath` of the `Workspace`. -/
@[inline] def getAugmentedLeanPath : m SearchPath :=
  (·.augmentedLeanPath) <$> getWorkspace

/-- Get the `augmentedLeanSrcPath` value of the `Workspace`. -/
@[inline] def getAugmentedLeanSrcPath  : m SearchPath :=
  (·.augmentedLeanSrcPath) <$> getWorkspace

/-- Get the `augmentedSharedLibPath` value of the `Workspace`. -/
@[inline] def getAugmentedSharedLibPath  : m SearchPath :=
  (·.augmentedSharedLibPath) <$> getWorkspace

/-- Get the `augmentedEnvVars` of the `Workspace`. -/
@[inline]  def getAugmentedEnv : m (Array (String × Option String)) :=
  (·.augmentedEnvVars) <$> getWorkspace

end

section
variable [MonadLakeEnv m] [Functor m]

/-! ## Environment Helpers -/

@[inline] def getLakeEnv : m Lake.Env :=
  read

/-! ### Lean Install Helpers -/

@[inline] def getLeanInstall : m LeanInstall :=
  (·.lean) <$> getLakeEnv

@[inline] def getLeanSysroot : m FilePath :=
  (·.sysroot) <$> getLeanInstall

@[inline] def getLeanSrcDir : m FilePath :=
  (·.srcDir) <$> getLeanInstall

/-- Get the `leanLibDir` of the detected `LeanInstall`. -/
@[inline] def getLeanLibDir : m FilePath :=
  (·.leanLibDir) <$> getLeanInstall

@[inline] def getLeanIncludeDir : m FilePath :=
  (·.includeDir) <$> getLeanInstall

@[inline] def getLeanSystemLibDir : m FilePath :=
  (·.systemLibDir) <$> getLeanInstall

@[inline] def getLean : m FilePath :=
  (·.lean) <$> getLeanInstall

@[inline] def getLeanc : m FilePath :=
  (·.leanc) <$> getLeanInstall

@[inline] def getLeanSharedLib : m FilePath :=
  (·.sharedLib) <$> getLeanInstall

@[inline] def getLeanAr : m FilePath :=
  (·.ar) <$> getLeanInstall

@[inline] def getLeanCc : m FilePath :=
  (·.cc) <$> getLeanInstall

@[inline] def getLeanCc? : m (Option String) :=
  (·.leanCc?) <$> getLeanInstall

/-! ### Lake Install Helpers -/

@[inline] def getLakeInstall : m LakeInstall :=
  (·.lake) <$> getLakeEnv

@[inline] def getLakeHome : m FilePath :=
  (·.home) <$> getLakeInstall

@[inline] def getLakeSrcDir : m FilePath :=
  (·.srcDir) <$> getLakeInstall

@[inline] def getLakeLibDir : m FilePath :=
  (·.libDir) <$> getLakeInstall

@[inline] def getLake : m FilePath :=
  (·.lake) <$> getLakeInstall

/-! ### Search Path Helpers -/

/-- Get the detected `LEAN_PATH` value of the Lake environment. -/
@[inline] def getEnvLeanPath : m SearchPath :=
  (·.leanPath) <$> getLakeEnv

/-- Get the detected `LEAN_SRC_PATH` value of the Lake environment. -/
@[inline] def getEnvLeanSrcPath : m SearchPath :=
  (·.leanSrcPath) <$> getLakeEnv

/-- Get the detected `sharedLibPathEnvVar` value of the Lake environment. -/
@[inline] def getEnvSharedLibPath : m SearchPath :=
  (·.sharedLibPath) <$> getLakeEnv

end
