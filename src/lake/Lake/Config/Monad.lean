/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Context
import Lake.Config.Workspace

open System
open Lean (Name NameMap)

/-! # Lake Configuration Monads
Definitions and helpers for interacting with the Lake configuration monads.
-/

namespace Lake

/-- A monad equipped with a (read-only) detected environment for Lake. -/
abbrev MonadLakeEnv (m : Type → Type u) :=
  MonadReaderOf Lake.Env m

/-- A transformer to equip a monad with a `Lake.Env`. -/
abbrev LakeEnvT := ReaderT Lake.Env

@[inline] def LakeEnvT.run (env : Lake.Env) (self : LakeEnvT m α) : m α :=
  ReaderT.run self env

/-- A monad equipped with a (read-only) Lake `Workspace`. -/
class MonadWorkspace (m : Type → Type u) where
  getWorkspace : m Workspace

export MonadWorkspace (getWorkspace)

instance [MonadReaderOf Workspace m] : MonadWorkspace m where
  getWorkspace := read

instance [MonadStateOf Workspace m] : MonadWorkspace m where
  getWorkspace := get

/-- A monad equipped with a (read-only) Lake context. -/
abbrev MonadLake (m : Type → Type u) :=
  MonadReaderOf Lake.Context m

/-- Make a `Lake.Context` from a `Workspace`. -/
@[inline] def mkLakeContext (ws : Workspace) : Lake.Context where
  opaqueWs := ws

/-- Run a `LakeT` monad in the context of this workspace. -/
@[inline] def Workspace.runLakeT (ws : Workspace) (x : LakeT m α) : m α :=
  x.run (mkLakeContext ws)

instance [MonadWorkspace m] [Functor m] : MonadLake m where
  read := (mkLakeContext ·) <$> getWorkspace

@[inline] def Context.workspace (self : Context) :=
  self.opaqueWs.get

instance [MonadLake m] [Functor m] : MonadWorkspace m where
  getWorkspace := (·.workspace) <$> read

instance [MonadWorkspace m] [Functor m] : MonadLakeEnv m where
  read := (·.lakeEnv) <$> getWorkspace

section
variable [MonadWorkspace m]

/-! ## Workspace Helpers -/

variable [Functor m]

/-- Get the root package of the context's workspace. -/
@[inline] def getRootPackage : m Package :=
  (·.root) <$> getWorkspace

@[inherit_doc Workspace.findPackage?, inline]
def findPackage? (name : Name) : m (Option (NPackage name)) :=
  (·.findPackage? name) <$> getWorkspace

@[inherit_doc Workspace.findModule?, inline]
def findModule? (name : Name) : m (Option Module) :=
  (·.findModule? name) <$> getWorkspace

@[inherit_doc Workspace.findLeanExe?, inline]
def findLeanExe? (name : Name) : m (Option LeanExe) :=
  (·.findLeanExe? name) <$> getWorkspace

@[inherit_doc Workspace.findLeanLib?, inline]
def findLeanLib? (name : Name) : m (Option LeanLib) :=
  (·.findLeanLib? name) <$> getWorkspace

@[inherit_doc Workspace.findExternLib?, inline]
def findExternLib? (name : Name) : m (Option ExternLib) :=
  (·.findExternLib? name) <$> getWorkspace

/-- Get the paths added to `LEAN_PATH` by the context's workspace. -/
@[inline] def getLeanPath : m SearchPath :=
  (·.leanPath) <$> getWorkspace

/-- Get the paths added to `LEAN_SRC_PATH` by the context's workspace. -/
@[inline] def getLeanSrcPath : m SearchPath :=
  (·.leanSrcPath) <$> getWorkspace

/-- Get the paths added to the shared library path by the context's workspace. -/
@[inline] def getSharedLibPath : m SearchPath :=
  (·.sharedLibPath) <$> getWorkspace

/-- Get the augmented `LEAN_PATH` set by the context's workspace. -/
@[inline] def getAugmentedLeanPath : m SearchPath :=
  (·.augmentedLeanPath) <$> getWorkspace

/-- Get the augmented `LEAN_SRC_PATH` set by the context's workspace. -/
@[inline] def getAugmentedLeanSrcPath  : m SearchPath :=
  (·.augmentedLeanSrcPath) <$> getWorkspace

/-- Get the augmented shared library path set by the context's workspace. -/
@[inline] def getAugmentedSharedLibPath  : m SearchPath :=
  (·.augmentedSharedLibPath) <$> getWorkspace

/-- Get the augmented environment variables set by the context's workspace. -/
@[inline]  def getAugmentedEnv : m (Array (String × Option String)) :=
  (·.augmentedEnvVars) <$> getWorkspace

end

section
variable [MonadLakeEnv m]

/-! ## Environment Helpers -/

@[inline] def getLakeEnv : m Lake.Env :=
  read

variable [Functor m]

/-- Get the `LAKE_NO_CACHE`/`--no-cache` Lake configuration. -/
@[inline] def getNoCache [Functor m] [MonadBuild m] : m Bool :=
  (·.noCache) <$> getLakeEnv

/-- Get whether the `LAKE_NO_CACHE`/`--no-cache` Lake configuration is **NOT** set. -/
@[inline] def getTryCache [Functor m] [MonadBuild m] : m Bool :=
  (!·.noCache) <$> getLakeEnv

/-- Get the `LAKE_PACKAGE_URL_MAP` for the Lake environment. Empty if none. -/
@[inline] def getPkgUrlMap : m (NameMap String) :=
  (·.pkgUrlMap) <$> getLakeEnv

/-- Get the name of Elan toolchain for the Lake environment. Empty if none. -/
@[inline] def getElanToolchain : m String :=
  (·.toolchain) <$> getLakeEnv

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

/-! ### Elan Install Helpers -/

/-- Get the detected Elan installation (if one). -/
@[inline] def getElanInstall? : m (Option ElanInstall) :=
  (·.elan?) <$> getLakeEnv

/-- Get the root directory of the detected Elan installation (i.e., `ELAN_HOME`). -/
@[inline] def getElanHome? : m (Option FilePath) :=
  (·.map (·.home)) <$> getElanInstall?

/-- Get the path of the `elan` binary in the detected Elan installation. -/
@[inline] def getElan? : m (Option FilePath) :=
  (·.map (·.elan)) <$> getElanInstall?

/-! ### Lean Install Helpers -/

/-- Get the detected Lean installation. -/
@[inline] def getLeanInstall : m LeanInstall :=
  (·.lean) <$> getLakeEnv

/-- Get the root directory of the detected Lean installation. -/
@[inline] def getLeanSysroot : m FilePath :=
  (·.sysroot) <$> getLeanInstall

/-- Get the Lean source directory of the detected Lean installation. -/
@[inline] def getLeanSrcDir : m FilePath :=
  (·.srcDir) <$> getLeanInstall

/-- Get the Lean library directory of the detected Lean installation. -/
@[inline] def getLeanLibDir : m FilePath :=
  (·.leanLibDir) <$> getLeanInstall

/-- Get the C include directory of the detected Lean installation. -/
@[inline] def getLeanIncludeDir : m FilePath :=
  (·.includeDir) <$> getLeanInstall

/-- Get the system library directory of the detected Lean installation. -/
@[inline] def getLeanSystemLibDir : m FilePath :=
  (·.systemLibDir) <$> getLeanInstall

/-- Get the path of the `lean` binary in the detected Lean installation. -/
@[inline] def getLean : m FilePath :=
  (·.lean) <$> getLeanInstall

/-- Get the path of the `leanc` binary in the detected Lean installation. -/
@[inline] def getLeanc : m FilePath :=
  (·.leanc) <$> getLeanInstall

/-- Get the path of the `libleanshared` library in the detected Lean installation. -/
@[inline] def getLeanSharedLib : m FilePath :=
  (·.sharedLib) <$> getLeanInstall

/-- Get the path of the `ar` binary in the detected Lean installation. -/
@[inline] def getLeanAr : m FilePath :=
  (·.ar) <$> getLeanInstall

/-- Get the path of C compiler in the detected Lean installation. -/
@[inline] def getLeanCc : m FilePath :=
  (·.cc) <$> getLeanInstall

/-- Get the optional `LEAN_CC` compiler override of the detected Lean installation. -/
@[inline] def getLeanCc? : m (Option String) :=
  (·.leanCc?) <$> getLeanInstall

/-! ### Lake Install Helpers -/

/-- Get the detected Lake installation. -/
@[inline] def getLakeInstall : m LakeInstall :=
  (·.lake) <$> getLakeEnv

/-- Get the root directory of the detected Lake installation (e.g., `LAKE_HOME`). -/
@[inline] def getLakeHome : m FilePath :=
  (·.home) <$> getLakeInstall

/-- Get the source directory of the detected Lake installation. -/
@[inline] def getLakeSrcDir : m FilePath :=
  (·.srcDir) <$> getLakeInstall

/-- Get the Lean library directory of the detected Lake installation. -/
@[inline] def getLakeLibDir : m FilePath :=
  (·.libDir) <$> getLakeInstall

/-- Get the path of the `lake` binary in the detected Lake installation. -/
@[inline] def getLake : m FilePath :=
  (·.lake) <$> getLakeInstall

end
