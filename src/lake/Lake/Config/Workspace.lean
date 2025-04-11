/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lean.Util.Paths
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig
import Lake.Config.Env
import Lake.Util.Log

open System

namespace Lake
open Lean (Name)

/-- A Lake workspace -- the top-level package directory. -/
structure Workspace : Type where
  /-- The root package of the workspace. -/
  root : Package
  /-- The detected `Lake.Env` of the workspace. -/
  lakeEnv : Lake.Env
  /--
  The CLI arguments Lake was run with.
  Used by `lake update` to perform a restart of Lake on a toolchain update.
  A value of `none` means that Lake is not restartable via the CLI.
  -/
  lakeArgs? : Option (Array String) := none
  /-- The packages within the workspace (in `require` declaration order). -/
  packages : Array Package := {}
  /-- Name-package map of packages within the workspace. -/
  packageMap : DNameMap NPackage := {}
  /-- Configuration map of facets defined in the workspace. -/
  facetConfigs : DNameMap FacetConfig := {}

instance : Nonempty Workspace :=
  have : Inhabited Package := Classical.inhabited_of_nonempty inferInstance
  ⟨by constructor <;> exact default⟩

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

/-- The full path to the workspace's Lake directory (e.g., `.lake`). -/
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

/-- The path to the workspace file used to configure automatic package overloads. -/
@[inline] def packageOverridesFile (self : Workspace) : FilePath :=
  self.lakeDir / "package-overrides.json"

/-- Add a package to the workspace. -/
def addPackage (pkg : Package) (self : Workspace) : Workspace :=
  {self with packages := self.packages.push pkg, packageMap := self.packageMap.insert pkg.name pkg}

/-- Try to find a package within the workspace with the given name. -/
@[inline] protected def findPackage? (name : Name) (self : Workspace) : Option (NPackage name) :=
  self.packageMap.find? name

/-- Try to find a script in the workspace with the given name. -/
protected def findScript? (script : Name) (self : Workspace) : Option Script :=
  self.packages.findSome? (·.scripts.find? script)

/-- Check if the module is local to any package in the workspace. -/
def isLocalModule (mod : Name) (self : Workspace) : Bool :=
  self.packages.any fun pkg => pkg.isLocalModule mod

/-- Check if the module is buildable by any package in the workspace. -/
def isBuildableModule (mod : Name) (self : Workspace) : Bool :=
  self.packages.any fun pkg => pkg.isBuildableModule mod

/-- Locate the named, buildable, importable, local module in the workspace. -/
protected def findModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packages.findSome? (·.findModule? mod)

/-- Locate the named, buildable, but not necessarily importable, module in the workspace. -/
def findTargetModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packages.findSome? (·.findTargetModule? mod)

/-- Returns the buildable module in the workspace whose source file is `path`.  -/
def findModuleBySrc? (path : FilePath) (self : Workspace) : Option Module :=
  self.packages.findSome? (·.findModuleBySrc? path)

/-- Try to find a Lean library in the workspace with the given name. -/
protected def findLeanLib? (name : Name) (self : Workspace) : Option LeanLib :=
  self.packages.findSome? fun pkg => pkg.findLeanLib? name

/-- Try to find a Lean executable in the workspace with the given name. -/
protected def findLeanExe? (name : Name) (self : Workspace) : Option LeanExe :=
  self.packages.findSome? fun pkg => pkg.findLeanExe? name

/-- Try to find an external library in the workspace with the given name. -/
protected def findExternLib? (name : Name) (self : Workspace) : Option ExternLib :=
  self.packages.findSome? fun pkg => pkg.findExternLib? name

/-- Try to find a target configuration in the workspace with the given name. -/
def findTargetConfig? (name : Name) (self : Workspace) : Option ((pkg : Package) × TargetConfig pkg.name name) :=
  self.packages.findSome? fun pkg => pkg.findTargetConfig? name <&> (⟨pkg, ·⟩)

/-- Try to find a target declaration in the workspace with the given name.  -/
def findTargetDecl? (name : Name) (self : Workspace) : Option ((pkg : Package) × NConfigDecl pkg.name name) :=
  self.packages.findSome? fun pkg => pkg.findTargetDecl? name <&> (⟨pkg, ·⟩)

/-- Add a facet to the workspace. -/
def addFacetConfig {name} (cfg : FacetConfig name) (self : Workspace) : Workspace :=
  {self with facetConfigs := self.facetConfigs.insert name cfg}

/-- Try to find a facet configuration in the workspace with the given name. -/
def findFacetConfig? (name : Name) (self : Workspace) : Option (FacetConfig name) :=
  self.facetConfigs.find? name

/-- Add a module facet to the workspace. -/
def addModuleFacetConfig (cfg : ModuleFacetConfig name) (self : Workspace) : Workspace :=
  self.addFacetConfig cfg.toFacetConfig

/-- Try to find a module facet configuration in the workspace with the given name. -/
def findModuleFacetConfig? (name : Name) (self : Workspace) : Option (ModuleFacetConfig name) :=
  self.findFacetConfig? name |>.bind (·.toKind? Module.facetKind)

/-- Add a package facet to the workspace. -/
def addPackageFacetConfig (cfg : PackageFacetConfig name) (self : Workspace) : Workspace :=
  self.addFacetConfig cfg.toFacetConfig

/-- Try to find a package facet configuration in the workspace with the given name. -/
def findPackageFacetConfig? (name : Name) (self : Workspace) : Option (PackageFacetConfig name) :=
  self.findFacetConfig? name |>.bind (·.toKind? Package.facetKind)

/-- Add a library facet to the workspace. -/
def addLibraryFacetConfig (cfg : LibraryFacetConfig name) (self : Workspace) : Workspace :=
  self.addFacetConfig cfg.toFacetConfig

/-- Try to find a library facet configuration in the workspace with the given name. -/
def findLibraryFacetConfig? (name : Name) (self : Workspace) : Option (LibraryFacetConfig name) :=
  self.findFacetConfig? name |>.bind (·.toKind? LeanLib.facetKind)

/-- The workspace's binary directories (which are added to `Path`). -/
def binPath (self : Workspace) : SearchPath :=
  self.packages.foldl (fun dirs pkg => pkg.binDir :: dirs) []

/-- The workspace's Lean library directories (which are added to `LEAN_PATH`). -/
def leanPath (self : Workspace) : SearchPath :=
  self.packages.foldl (fun dirs pkg => pkg.leanLibDir :: dirs) []

/-- The workspace's source directories (which are added to `LEAN_SRC_PATH`). -/
def leanSrcPath (self : Workspace) : SearchPath :=
  self.packages.foldl (init := {}) fun dirs pkg =>
    pkg.targetDecls.foldr (init := dirs) fun cfg dirs =>
      if let some cfg := cfg.leanLibConfig? then
        pkg.srcDir / cfg.srcDir :: dirs
      else
        dirs

/--
The workspace's shared library path (e.g., for `--load-dynlib`).
This is added to the `sharedLibPathEnvVar` by `lake env`.
-/
def sharedLibPath (self : Workspace) : SearchPath :=
   self.packages.foldr (fun pkg dirs => pkg.sharedLibDir :: dirs) []

/--
The detected `PATH` of the environment augmented with
the workspace's `binDir` and Lean and Lake installations' `binDir`.
On Windows, also adds the workspace shared library path.
-/
def augmentedPath (self : Workspace) : SearchPath :=
  if Platform.isWindows then
    self.binPath ++ self.sharedLibPath ++ self.lakeEnv.path
  else
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

The order is Lean's, the workspace's, and then the enviroment's.
Lean's comes first because Lean needs to load its own shared libraries from this path.
Giving the workspace greater precedence can break this (e.g., when bootstrapping),
-/
def augmentedSharedLibPath (self : Workspace) : SearchPath :=
  self.lakeEnv.lean.sharedLibPath ++ self.sharedLibPath ++ self.lakeEnv.initSharedLibPath

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
