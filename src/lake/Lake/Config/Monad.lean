/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Workspace

set_option doc.verso true

open System
open Lean (Name NameMap LeanOptions)

/-! # Lake Configuration Monads
Definitions and helpers for interacting with the Lake configuration monads.
-/

namespace Lake

/-- A monad equipped with a (read-only) detected environment for Lake. -/
public abbrev MonadLakeEnv (m : Type → Type u) :=
  MonadReaderOf Lake.Env m

/-- A transformer to equip a monad with a {lean}`Lake.Env`. -/
public abbrev LakeEnvT := ReaderT Lake.Env

@[inline] public def LakeEnvT.run (env : Lake.Env) (self : LakeEnvT m α) : m α :=
  ReaderT.run self env

/-- A monad equipped with a (read-only) Lake {lean}`Workspace`. -/
public class MonadWorkspace (m : Type → Type u) where
  /-- Gets the current Lake workspace. -/
  getWorkspace : m Workspace

export MonadWorkspace (getWorkspace)

public instance [MonadReaderOf Workspace m] : MonadWorkspace m where
  getWorkspace := read

public instance [MonadStateOf Workspace m] : MonadWorkspace m where
  getWorkspace := get

/-- A monad equipped with a (read-only) Lake context. -/
public abbrev MonadLake (m : Type → Type u) :=
  MonadReaderOf Lake.Context m

/-- Constructs a {lean}`Lake.Context` from  the workspace {lean}`ws`. -/
@[inline] public def mkLakeContext (ws : Workspace) : Lake.Context where
  opaqueWs := ws

/-- Runs a {lean}`LakeT` monad in the context of the workspace {lean}`ws`. -/
@[inline] public def Workspace.runLakeT (ws : Workspace) (x : LakeT m α) : m α :=
  x.run (mkLakeContext ws)

public instance [MonadWorkspace m] [Functor m] : MonadLake m where
  read := (mkLakeContext ·) <$> getWorkspace

@[inline] public def Context.workspace (self : Context) :=
  self.opaqueWs.get

public instance [MonadLake m] [Functor m] : MonadWorkspace m where
  getWorkspace := (·.workspace) <$> read

public instance [MonadWorkspace m] [Functor m] : MonadLakeEnv m where
  read := (·.lakeEnv) <$> getWorkspace

section
variable [MonadWorkspace m]

/-! ## Workspace Helpers -/

variable [Functor m]

/-- Returns the root package of the context's workspace. -/
@[inline] public def getRootPackage : m Package :=
  (·.root) <$> getWorkspace

@[inherit_doc Workspace.findPackageByKey?, inline]
public def findPackageByKey? (keyName : Name) : m (Option (NPackage keyName)) :=
  (·.findPackageByKey? keyName) <$> getWorkspace

/--
Returns the first package in the workspace (if any) that has been assigned the {lean}`name`.

This can be used to find the package corresponding to a user-provided name. If the package's unique
identifier is already available, use {name}`findPackageByKey?`instead.
-/
@[inline] public def findPackageByName? (name : Name) : m (Option Package) :=
  (·.findPackageByName? name) <$> getWorkspace

/--
**Deprecated.** If attempting to find the package corresponding to a user-provided name,
use {name (full := Workspace.findPackageByName?)}`findPackageByName?`. Otherwise, if the package's
unique identifier is available, use {name (full :=findPackageByKey?)}`findPackageByKey?`.
-/
@[deprecated "Use `findPackageByKey?` or `findPackageByName?` instead" (since := "2025-12-03")]
public abbrev findPackage? (name : Name) : m (Option (NPackage name)) := findPackageByKey? name

@[inherit_doc Workspace.findModule?, inline]
public def findModule? (name : Name) : m (Option Module) :=
  (·.findModule? name) <$> getWorkspace

@[inherit_doc Workspace.findModules, inline]
public def findModules (name : Name) : m (Array Module) :=
  (·.findModules name) <$> getWorkspace

@[inherit_doc Workspace.findModuleBySrc?, inline]
public def findModuleBySrc? (path : FilePath) : m (Option Module) :=
  (·.findModuleBySrc? path) <$> getWorkspace

@[inherit_doc Workspace.findLeanExe?, inline]
public def findLeanExe? (name : Name) : m (Option LeanExe) :=
  (·.findLeanExe? name) <$> getWorkspace

@[inherit_doc Workspace.findLeanLib?, inline]
public def findLeanLib? (name : Name) : m (Option LeanLib) :=
  (·.findLeanLib? name) <$> getWorkspace

@[inherit_doc Workspace.findExternLib?, inline]
public def findExternLib? (name : Name) : m (Option ExternLib) :=
  (·.findExternLib? name) <$> getWorkspace

@[inherit_doc Workspace.serverOptions, inline]
public def getServerOptions : m LeanOptions :=
  (·.serverOptions) <$> getWorkspace

@[inherit_doc Workspace.leanOptions, inline]
public def getLeanOptions : m LeanOptions :=
  (·.leanOptions) <$> getWorkspace

@[inherit_doc Workspace.leanArgs, inline]
public def getLeanArgs : m (Array String) :=
  (·.leanArgs) <$> getWorkspace

/-- Returns the paths added to {lit}`LEAN_PATH` by the context's workspace. -/
@[inline] public def getLeanPath : m SearchPath :=
  (·.leanPath) <$> getWorkspace

/-- Returns the paths added to {lit}`LEAN_SRC_PATH` by the context's workspace. -/
@[inline] public def getLeanSrcPath : m SearchPath :=
  (·.leanSrcPath) <$> getWorkspace

/-- Returns the paths added to the shared library path by the context's workspace. -/
@[inline] public def getSharedLibPath : m SearchPath :=
  (·.sharedLibPath) <$> getWorkspace

/-- Returns the augmented {lit}`LEAN_PATH` set by the context's workspace. -/
@[inline] public def getAugmentedLeanPath : m SearchPath :=
  (·.augmentedLeanPath) <$> getWorkspace

/-- Returns the augmented {lit}`LEAN_SRC_PATH` set by the context's workspace. -/
@[inline] public def getAugmentedLeanSrcPath  : m SearchPath :=
  (·.augmentedLeanSrcPath) <$> getWorkspace

/-- Returns the augmented shared library path set by the context's workspace. -/
@[inline] public def getAugmentedSharedLibPath  : m SearchPath :=
  (·.augmentedSharedLibPath) <$> getWorkspace

/-- Returns the augmented environment variables set by the context's workspace. -/
@[inline] public def getAugmentedEnv : m (Array (String × Option String)) :=
  (·.augmentedEnvVars) <$> getWorkspace

/-- Returns the Lake cache for the environment. -/
@[inline] public def getLakeCache : m Cache :=
  (·.lakeCache) <$> getWorkspace

@[inline, inherit_doc Cache.getArtifact?]
public def getArtifact? [Bind m] [MonadLiftT BaseIO m] (descr : ArtifactDescr) : m (Option Artifact) :=
  getLakeCache >>= (·.getArtifact? descr)

/--
Returns whether the package the artifact cache is enabled for the package.

If the package has not configured the artifact cache itself through
{lean}`Package.enableArtifactCache?`, this will default to the workspace configuration.
-/
public def Package.isArtifactCacheEnabled [MonadWorkspace m] (self : Package) : m Bool :=
  (self.enableArtifactCache?.getD ·.enableArtifactCache) <$> getWorkspace

end

section
variable [MonadLakeEnv m]

/-! ## Environment Helpers -/

/--
Gets the current Lake environment.
-/
@[inline] public def getLakeEnv : m Lake.Env :=
  read

variable [Functor m]

/-- Returns the {lit}`LAKE_NO_CACHE`/{lit}`--no-cache` Lake configuration. -/
@[inline] public def getNoCache [Functor m] [MonadBuild m] : m Bool :=
  (·.noCache) <$> getLakeEnv

/-- Returns whether the {lit}`LAKE_NO_CACHE`/{lit}`--no-cache` Lake configuration is **NOT** set. -/
@[inline] public def getTryCache [Functor m] [MonadBuild m] : m Bool :=
  (!·.noCache) <$> getLakeEnv

/-- Returns the {lit}`LAKE_PACKAGE_URL_MAP` for the Lake environment. Empty if none. -/
@[inline] public def getPkgUrlMap : m (NameMap String) :=
  (·.pkgUrlMap) <$> getLakeEnv

/-- Returns the name of Elan toolchain for the Lake environment. Empty if none. -/
@[inline] public def getElanToolchain : m String :=
  (·.toolchain) <$> getLakeEnv


/-! ### Search Path Helpers -/

/-- Returns the detected {lit}`LEAN_PATH` value of the Lake environment. -/
@[inline] public def getEnvLeanPath : m SearchPath :=
  (·.leanPath) <$> getLakeEnv

/-- Returns the detected {lit}`LEAN_SRC_PATH` value of the Lake environment. -/
@[inline] public def getEnvLeanSrcPath : m SearchPath :=
  (·.leanSrcPath) <$> getLakeEnv

/-- Returns the detected {lean}`sharedLibPathEnvVar` value of the Lake environment. -/
@[inline] public def getEnvSharedLibPath : m SearchPath :=
  (·.sharedLibPath) <$> getLakeEnv

/-! ### Elan Install Helpers -/

/-- Returns the detected Elan installation (if one). -/
@[inline] public def getElanInstall? : m (Option ElanInstall) :=
  (·.elan?) <$> getLakeEnv

/-- Returns the root directory of the detected Elan installation (i.e., {lit}`ELAN_HOME`). -/
@[inline] public def getElanHome? : m (Option FilePath) :=
  (·.map (·.home)) <$> getElanInstall?

/-- Returns the path of the {lit}`elan` binary in the detected Elan installation. -/
@[inline] public def getElan? : m (Option FilePath) :=
  (·.map (·.elan)) <$> getElanInstall?

/-! ### Lean Install Helpers -/

/-- Returns the detected Lean installation. -/
@[inline] public def getLeanInstall : m LeanInstall :=
  (·.lean) <$> getLakeEnv

/-- Returns the root directory of the detected Lean installation. -/
@[inline] public def getLeanSysroot : m FilePath :=
  (·.sysroot) <$> getLeanInstall

/-- Returns the Lean source directory of the detected Lean installation. -/
@[inline] public def getLeanSrcDir : m FilePath :=
  (·.srcDir) <$> getLeanInstall

/-- Returns the Lean library directory of the detected Lean installation. -/
@[inline] public def getLeanLibDir : m FilePath :=
  (·.leanLibDir) <$> getLeanInstall

/-- Returns the C include directory of the detected Lean installation. -/
@[inline] public def getLeanIncludeDir : m FilePath :=
  (·.includeDir) <$> getLeanInstall

/-- Returns the system library directory of the detected Lean installation. -/
@[inline] public def getLeanSystemLibDir : m FilePath :=
  (·.systemLibDir) <$> getLeanInstall

/-- Returns the path of the {lit}`lean` binary in the detected Lean installation. -/
@[inline] public def getLean : m FilePath :=
  (·.lean) <$> getLeanInstall

/-- Returns the path of the {lit}`leanc` binary in the detected Lean installation. -/
@[inline] public def getLeanc : m FilePath :=
  (·.leanc) <$> getLeanInstall

/-- Returns the path of the {lit}`libleanshared` library in the detected Lean installation. -/
@[inline] public def getLeanSharedLib : m FilePath :=
  (·.sharedLib) <$> getLeanInstall

/-- Get the path of the {lit}`ar` binary in the detected Lean installation. -/
@[inline] public def getLeanAr : m FilePath :=
  (·.ar) <$> getLeanInstall

/-- Get the path of C compiler in the detected Lean installation. -/
@[inline] public def getLeanCc : m FilePath :=
  (·.cc) <$> getLeanInstall

/-- Get the optional {lit}`LEAN_CC` compiler override of the detected Lean installation. -/
@[inline] public def getLeanCc? : m (Option String) :=
  (·.leanCc?) <$> getLeanInstall

/-- Get the flags required to link shared libraries using the detected Lean installation. -/
@[inline] public def getLeanLinkSharedFlags : m (Array String) :=
  (·.ccLinkSharedFlags) <$> getLeanInstall

/-! ### Lake Install Helpers -/

/-- Get the detected Lake installation. -/
@[inline] public def getLakeInstall : m LakeInstall :=
  (·.lake) <$> getLakeEnv

/-- Get the root directory of the detected Lake installation (e.g., {lit}`LAKE_HOME`). -/
@[inline] public def getLakeHome : m FilePath :=
  (·.home) <$> getLakeInstall

/-- Get the source directory of the detected Lake installation. -/
@[inline] public def getLakeSrcDir : m FilePath :=
  (·.srcDir) <$> getLakeInstall

/-- Get the Lean library directory of the detected Lake installation. -/
@[inline] public def getLakeLibDir : m FilePath :=
  (·.libDir) <$> getLakeInstall

/-- Get the path of the {lit}`lake` binary in the detected Lake installation. -/
@[inline] public def getLake : m FilePath :=
  (·.lake) <$> getLakeInstall

end
