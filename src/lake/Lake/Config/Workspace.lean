/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Paths
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig
import Lake.Config.Env
import Lake.Util.Log

open System

namespace Lake

/-- A Lake workspace -- the top-level package directory. -/
structure Workspace : Type where
  /-- The root package of the workspace. -/
  root : Package
  /-- The detect `Lake.Env` of the workspace. -/
  lakeEnv : Lake.Env
  /-- The packages within the workspace (in `require` declaration order). -/
  packages : Array Package := {}
  /-- Name-package map of packages within the workspace. -/
  packageMap : DNameMap NPackage := {}
  /-- Name-configuration map of module facets defined in the workspace. -/
  moduleFacetConfigs : DNameMap ModuleFacetConfig
  /-- Name-configuration map of package facets defined in the workspace. -/
  packageFacetConfigs : DNameMap PackageFacetConfig
  /-- Name-configuration map of library facets defined in the workspace. -/
  libraryFacetConfigs : DNameMap LibraryFacetConfig

instance : Nonempty Workspace :=
  have : Inhabited Package := Classical.inhabited_of_nonempty inferInstance
  by refine' ⟨{..}⟩ <;> exact default

hydrate_opaque_type OpaqueWorkspace Workspace

namespace Workspace

/-- The path to the workspace's directory (i.e., the directory of the root package). -/
@[inline] def dir (self : Workspace) : FilePath :=
  self.root.dir

/-- The workspace's configuration. -/
@[inline] def config (self : Workspace) : WorkspaceConfig :=
  self.root.config.toWorkspaceConfig

/-- The path to the workspace' Lake directory relative to `dir`. -/
@[inline] def relLakeDir (self : Workspace) : FilePath :=
  self.root.relLakeDir

/-- The the full path to the workspace's Lake directory (e.g., `.lake`). -/
@[inline] def lakeDir (self : Workspace) : FilePath :=
  self.root.lakeDir

/-- The path to the workspace's remote packages directory relative to `dir`. -/
@[inline] def relPkgsDir (self : Workspace) : FilePath :=
  self.root.relPkgsDir

/-- The workspace's `dir` joined with its `relPkgsDir`. -/
@[inline] def pkgsDir (self : Workspace) : FilePath :=
  self.root.pkgsDir

/-- The workspace's Lake manifest. -/
@[inline] def manifestFile (self : Workspace) : FilePath :=
  self.root.manifestFile

/-- Add a package to the workspace. -/
def addPackage (pkg : Package) (self : Workspace) : Workspace :=
  {self with packages := self.packages.push pkg, packageMap := self.packageMap.insert pkg.name pkg}

/-- Try to find a package within the workspace with the given name. -/
@[inline] def findPackage? (name : Name) (self : Workspace) : Option (NPackage name) :=
  self.packageMap.find? name

/-- Try to find a script in the workspace with the given name. -/
def findScript? (script : Name) (self : Workspace) : Option Script :=
  self.packages.findSomeRev? (·.scripts.find? script)

/-- Check if the module is local to any package in the workspace. -/
def isLocalModule (mod : Name) (self : Workspace) : Bool :=
  self.packages.any fun pkg => pkg.isLocalModule mod

/-- Check if the module is buildable by any package in the workspace. -/
def isBuildableModule (mod : Name) (self : Workspace) : Bool :=
  self.packages.any fun pkg => pkg.isBuildableModule mod

/-- Locate the named, buildable, importable, local module in the workspace. -/
def findModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packages.findSomeRev? (·.findModule? mod)

/-- Locate the named, buildable, but not necessarily importable, module in the workspace. -/
def findTargetModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packages.findSomeRev? (·.findTargetModule? mod)

/-- Try to find a Lean library in the workspace with the given name. -/
def findLeanLib? (name : Name) (self : Workspace) : Option LeanLib :=
  self.packages.findSomeRev? fun pkg => pkg.findLeanLib? name

/-- Try to find a Lean executable in the workspace with the given name. -/
def findLeanExe? (name : Name) (self : Workspace) : Option LeanExe :=
  self.packages.findSomeRev? fun pkg => pkg.findLeanExe? name

/-- Try to find an external library in the workspace with the given name. -/
def findExternLib? (name : Name) (self : Workspace) : Option ExternLib :=
  self.packages.findSomeRev? fun pkg => pkg.findExternLib? name

/-- Try to find a target configuration in the workspace with the given name. -/
def findTargetConfig? (name : Name) (self : Workspace) : Option ((pkg : Package) × TargetConfig pkg.name name) :=
  self.packages.findSomeRev? fun pkg => pkg.findTargetConfig? name <&> (⟨pkg, ·⟩)

/-- Add a module facet to the workspace. -/
def addModuleFacetConfig (cfg : ModuleFacetConfig name) (self : Workspace) : Workspace :=
  {self with moduleFacetConfigs := self.moduleFacetConfigs.insert name cfg}

/-- Try to find a module facet configuration in the workspace with the given name. -/
@[inline] def findModuleFacetConfig? (name : Name) (self : Workspace) : Option (ModuleFacetConfig name) :=
  self.moduleFacetConfigs.find? name

/-- Add a package facet to the workspace. -/
def addPackageFacetConfig (cfg : PackageFacetConfig name) (self : Workspace) : Workspace :=
  {self with packageFacetConfigs := self.packageFacetConfigs.insert name cfg}

/-- Try to find a package facet configuration in the workspace with the given name. -/
@[inline] def findPackageFacetConfig? (name : Name) (self : Workspace) : Option (PackageFacetConfig name) :=
  self.packageFacetConfigs.find? name

/-- Add a library facet to the workspace. -/
def addLibraryFacetConfig (cfg : LibraryFacetConfig name) (self : Workspace) : Workspace :=
  {self with libraryFacetConfigs := self.libraryFacetConfigs.insert cfg.name cfg}

/-- Try to find a library facet configuration in the workspace with the given name. -/
@[inline] def findLibraryFacetConfig? (name : Name) (self : Workspace) : Option (LibraryFacetConfig name) :=
  self.libraryFacetConfigs.find? name

/-- The workspace's binary directories (which are added to `Path`). -/
def binPath (self : Workspace) : SearchPath :=
  self.packages.foldr (fun pkg dirs => pkg.binDir :: dirs) []

/-- The workspace's Lean library directories (which are added to `LEAN_PATH`). -/
def leanPath (self : Workspace) : SearchPath :=
  self.packages.foldr (fun pkg dirs => pkg.leanLibDir :: dirs) []

/-- The workspace's source directories (which are added to `LEAN_SRC_PATH`). -/
def leanSrcPath (self : Workspace) : SearchPath :=
  self.packages.foldr (init := {}) fun pkg dirs =>
    pkg.leanLibConfigs.foldr (init := dirs) fun cfg dirs =>
        pkg.srcDir / cfg.srcDir :: dirs

/--
The workspace's shared library path (e.g., for `--load-dynlib`).
This is added to the `sharedLibPathEnvVar` by `lake env`.
-/
def sharedLibPath (self : Workspace) : SearchPath :=
   self.packages.foldr (fun pkg dirs => pkg.nativeLibDir :: dirs) []

/--
The detected `PATH` of the environment augmented with
the workspace's `binDir` and Lean and Lake installations' `binDir`.
-/
def augmentedPath (self : Workspace) : SearchPath :=
  self.binPath ++ self.lakeEnv.path

/--
The detected `LEAN_PATH` of the environment augmented with
the workspace's `leanPath` and Lake's `libDir`.
-/
def augmentedLeanPath (self : Workspace) : SearchPath :=
  self.leanPath ++ self.lakeEnv.leanPath

/--
The detected `LEAN_SRC_PATH` of the environment augmented with
the workspace's `leanSrcPath` and Lake's `srcDir`.
-/
def augmentedLeanSrcPath (self : Workspace) : SearchPath :=
  self.leanSrcPath ++ self.lakeEnv.leanSrcPath

/-
The detected `sharedLibPathEnv` value of the environment augmented with
the workspace's `libPath` and Lean installation's shared library directories.
-/
def augmentedSharedLibPath (self : Workspace) : SearchPath :=
  self.sharedLibPath ++ self.lakeEnv.sharedLibPath

/--
The detected environment augmented with Lake's and the workspace's paths.
These are the settings use by `lake env` / `Lake.env` to run executables.
-/
def augmentedEnvVars (self : Workspace) : Array (String × Option String) :=
  let vars := self.lakeEnv.baseVars ++ #[
    ("LEAN_PATH", some self.augmentedLeanPath.toString),
    ("LEAN_SRC_PATH", some self.augmentedLeanSrcPath.toString),
    ("PATH", some self.augmentedPath.toString)
  ]
  if Platform.isWindows then
    vars
  else
    vars.push (sharedLibPathEnvVar, some self.augmentedSharedLibPath.toString)

/-- Remove all packages' build outputs (i.e., delete their build directories). -/
def clean (self : Workspace) : IO Unit := do
  self.packages.forM fun pkg => pkg.clean
