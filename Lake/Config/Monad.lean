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

variable [MonadLake m]

def getLeanEnv [Monad m] : m (Array (String × Option String)) := do
  let ws ← getWorkspace
  let lean ← getLeanInstall
  return #[
    ("LEAN_SYSROOT", lean.sysroot.toString),
    ("LEAN_AR", lean.ar.toString),
    ("LEAN_CC", lean.cc.toString),
    ("LEAN_PATH", ws.oleanPath.toString),
    ("LEAN_SRC_PATH", ws.leanSrcPath.toString)
  ]

variable [Functor m]

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

@[inline] def getOleanPath : m SearchPath :=
  (·.oleanPath) <$> getWorkspace

@[inline] def getLeanSysroot : m FilePath :=
  (·.sysroot) <$> getLeanInstall

@[inline] def getLeanLibDir : m FilePath :=
  (·.libDir) <$> getLeanInstall

@[inline] def getLeanOleanDir : m FilePath :=
  (·.oleanDir) <$> getLeanInstall

@[inline] def getLeanIncludeDir : m FilePath :=
  (·.includeDir) <$> getLeanInstall

@[inline] def getLean : m FilePath :=
  (·.lean) <$> getLeanInstall

@[inline] def getLeanc : m FilePath :=
  (·.leanc) <$> getLeanInstall

@[inline] def getLeanAr : m FilePath :=
  (·.ar) <$> getLeanInstall

@[inline] def getLeanCc : m FilePath :=
  (·.cc) <$> getLeanInstall

@[inline] def getLakeOleanDir : m FilePath :=
  (·.oleanDir) <$> getLakeInstall
