/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Context
import Lake.Config.InstallPath
import Lake.Config.Workspace

open System
open Lean (Name)

namespace Lake

deriving instance Inhabited for Context

class MonadLake (m : Type → Type u) where
  getLeanInstall : m LeanInstall
  getLakeInstall : m LakeInstall
  getWorkspace : m Workspace

export MonadLake (getLeanInstall getLakeInstall getWorkspace)

instance [MonadLift m n] [MonadLake m] : MonadLake n where
  getLeanInstall := liftM (m := m) <| getLeanInstall
  getLakeInstall := liftM (m := m) <| getLakeInstall
  getWorkspace := liftM (m := m) <| getWorkspace

@[inline] def Context.workspace (self : Context) :=
  self.opaqueWs.get

instance [Monad m] : MonadLake (LakeT m) where
  getLeanInstall := (·.lean) <$> read
  getLakeInstall := (·.lake) <$> read
  getWorkspace := (·.workspace) <$> read

instance [MonadLake m] [Monad m] [MonadLiftT n m] : MonadLiftT (LakeT n) m where
  monadLift x := do
    liftM <| x {
      lean := ← getLeanInstall
      lake := ← getLakeInstall
      opaqueWs := ← getWorkspace
    }

section
variable [MonadLake m] [Functor m]

/- ## Workspace Helpers -/

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

@[inline] def getLeanPath : m SearchPath :=
  (·.oleanPath) <$> getWorkspace

@[inline] def getLeanSrcPath : m SearchPath :=
  (·.leanSrcPath) <$> getWorkspace

@[inline] def getLibPath : m SearchPath :=
  (·.libPath) <$> getWorkspace

/- ## Lean Install Helpers -/

@[inline] def getLeanSysroot : m FilePath :=
  (·.sysroot) <$> getLeanInstall

@[inline] def getLeanSrcDir : m FilePath :=
  (·.srcDir) <$> getLeanInstall

@[inline] def getLeanOleanDir : m FilePath :=
  (·.oleanDir) <$> getLeanInstall

@[inline] def getLeanIncludeDir : m FilePath :=
  (·.includeDir) <$> getLeanInstall

@[inline] def getLeanLibDir : m FilePath :=
  (·.libDir) <$> getLeanInstall

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

/- ## Lake Install Helpers -/

@[inline] def getLakeHome : m FilePath :=
  (·.home) <$> getLakeInstall

@[inline] def getLakeSrcDir : m FilePath :=
  (·.srcDir) <$> getLakeInstall

@[inline] def getLakeOleanDir : m FilePath :=
  (·.oleanDir) <$> getLakeInstall

@[inline] def getLake : m FilePath :=
  (·.lake) <$> getLakeInstall

end

/--
Get `LEAN_PATH` augmented with the workspace's `leanPath` and Lake's `oleanDir`.

Including Lake's `oleanDir` at the end ensures that same Lake package being
used to build is available to the environment (and thus, e.g., the Lean server).
Otherwise, it may fall back on whatever the default Lake instance is.
-/
@[inline] def getAugmentedLeanPath : LakeT BaseIO SearchPath := do
  return (← getSearchPath "LEAN_PATH") ++ (← getLeanPath) ++ [← getLakeOleanDir]

/--
Get `LEAN_SRC_PATH` augmented with the workspace's `leanSrcPath` and Lake's `srcDir`.

Including Lake's `srcDir` at the end ensures that same Lake package being
used to build is available to the environment (and thus, e.g., the Lean server).
Otherwise, it may fall back on whatever the default Lake instance is.
-/
@[inline] def getAugmentedLeanSrcPath : LakeT BaseIO SearchPath := do
  return (← getSearchPath "LEAN_SRC_PATH") ++ (← getLeanSrcPath) ++ [← getLakeSrcDir]

/- Get `sharedLibPathEnv` augmented with the workspace's `libPath`. -/
@[inline] def getAugmentedLibPath : LakeT BaseIO SearchPath := do
  return (← getSearchPath sharedLibPathEnvVar) ++ (← getLibPath)

def getAugmentedEnv : LakeT BaseIO (Array (String × Option String)) :=
  return mkInstallEnv (← getLeanInstall) (← getLakeInstall) ++ #[
    ("LEAN_PATH", some (← getAugmentedLeanPath).toString),
    ("LEAN_SRC_PATH", some (← getAugmentedLeanSrcPath).toString),
    (sharedLibPathEnvVar, some (← getAugmentedLibPath).toString)
  ]
