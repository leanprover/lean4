/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Paths
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig
import Lake.Config.Env

open System
open Lean (LeanPaths)

namespace Lake

/-- The file name of a workspace's package manifest (i.e., `manifest.json`). -/
def manifestFileName := "manifest.json"

/-- A Lake workspace -- the top-level package directory. -/
structure Workspace where
  /-- The root package of the workspace. -/
  root : Package
  /-- The detect `Lake.Env` of the workspace. -/
  env : Lake.Env
  /-- Name-package map of packages within the workspace. -/
  packageMap : NameMap Package := {}
  deriving Inhabited

hydrate_opaque_type OpaqueWorkspace Workspace

namespace Workspace

/-- The path to the workspace's directory (i.e., the directory of the root package). -/
def dir (self : Workspace) : FilePath :=
  self.root.dir

/-- The workspace's configuration. -/
def config (self : Workspace) : WorkspaceConfig :=
  self.root.config.toWorkspaceConfig

/-- The workspace's `dir` joined with its `packagesDir` configuration. -/
def packagesDir (self : Workspace) : FilePath :=
  self.dir / self.config.packagesDir

/-- The workspace's JSON manifest of packages. -/
def manifestFile (self : Workspace) : FilePath :=
  self.packagesDir / manifestFileName

/-- The `List` of packages to the workspace. -/
def packageList (self : Workspace) : List Package :=
  self.packageMap.revFold (fun pkgs _ pkg => pkg :: pkgs) []

/-- The `Array` of packages to the workspace. -/
def packageArray (self : Workspace) : Array Package :=
  self.packageMap.fold (fun pkgs _ pkg => pkgs.push pkg) #[]

/-- Add a package to the workspace. -/
def addPackage (pkg : Package) (self : Workspace) : Workspace :=
  {self with packageMap := self.packageMap.insert pkg.name pkg}

/-- Get a package within the workspace by name. -/
def findPackage? (pkg : Name) (self : Workspace) : Option Package :=
  self.packageMap.find? pkg

/-- Check if the module is local to any package in the workspace. -/
def isLocalModule (mod : Name) (self : Workspace) : Bool :=
  self.packageMap.any fun _ pkg => pkg.isLocalModule mod

/-- Check if the module is buildable by any package in the workspace. -/
def isBuildableModule (mod : Name) (self : Workspace) : Bool :=
  self.packageMap.any fun _ pkg => pkg.isBuildableModule mod

/-- Locate the named module in the workspace (if it is local to it). -/
def findModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packageArray.findSome? (·.findModule? mod)

/-- Try to find a Lean library in the workspace with the given name. -/
def findLeanLib? (name : Name) (self : Workspace) : Option LeanLib :=
  self.packageArray.findSome? fun pkg => pkg.findLeanLib? name

/-- Try to find a Lean executable in the workspace with the given name. -/
def findLeanExe? (name : Name) (self : Workspace) : Option LeanExe :=
  self.packageArray.findSome? fun pkg => pkg.findLeanExe? name

/-- Try to find an external library in the workspace with the given name. -/
def findExternLib? (name : Name) (self : Workspace) : Option ExternLib :=
  self.packageArray.findSome? fun pkg => pkg.findExternLib? name

/-- Try to find a module facet configuration in the workspace with the given name. -/
def findModuleFacetConfig? (name : WfName) (self : Workspace) : Option (ModuleFacetConfig name) :=
  self.packageArray.findSome? fun pkg => pkg.findModuleFacetConfig? name

/-- Try to find a package facet configuration in the workspace with the given name. -/
def findPackageFacetConfig? (name : WfName) (self : Workspace) : Option (PackageFacetConfig name) :=
  self.packageArray.findSome? fun pkg => pkg.findPackageFacetConfig? name

/-- Try to find a target configuration in the workspace with the given name. -/
def findTargetConfig? (name : Name) (self : Workspace) : Option (Package × TargetConfig) :=
  self.packageArray.findSome? fun pkg => pkg.findTargetConfig? name <&> (⟨pkg, ·⟩)

/-- The `LEAN_PATH` of the workspace. -/
def leanPath (self : Workspace) : SearchPath :=
  self.packageList.map (·.oleanDir)

/-- The `LEAN_SRC_PATH` of the workspace. -/
def leanSrcPath (self : Workspace) : SearchPath :=
  self.packageList.map (·.srcDir)

/--
The shared library path of the workspace (e.g., for `--load-dynlib`).
This is added to the `sharedLibPathEnvVar` by `lake env`.
-/
def libPath (self : Workspace) : SearchPath :=
  self.packageList.map (·.libDir)

/-- The `LeanPaths` of the workspace. -/
def leanPaths (self : Workspace) : LeanPaths where
  oleanPath := self.packageList.map (·.oleanDir)
  srcPath := self.packageList.map (·.srcDir)

/--
Rhe detected `LEAN_PATH` of the environment
augmented with the workspace's `leanPath` and Lake's `libDir`.

We include Lake's `oleanDir` at the end to ensure that same Lake package being
used to build is available to the environment (and thus, e.g., the Lean server).
Otherwise, it may fall back on whatever the default Lake instance is.
-/
def augmentedLeanPath (self : Workspace) : SearchPath :=
  self.env.leanPath ++ self.leanPath ++ [self.env.lake.libDir]

/--
The detected `LEAN_SRC_PATH` of the environment
augmented with the workspace's `leanSrcPath` and Lake's `srcDir`.

We include Lake's `srcDir` at the end to ensure that same Lake package being
used to build is available to the environment (and thus, e.g., the Lean server).
Otherwise, it may fall back on whatever the default Lake instance is.
-/
def augmentedLeanSrcPath (self : Workspace) : SearchPath :=
  self.env.leanSrcPath ++ self.leanSrcPath ++ [self.env.lake.srcDir]

/-
The detected `sharedLibPathEnv` value of the environment
augmented with the workspace's `libPath`.
-/
def augmentedSharedLibPath (self : Workspace) : SearchPath :=
  self.env.sharedLibPath ++ self.libPath

/--
The detected environment augmented with the Workspace's paths.
These are the settings use by `lake env` / `Lake.env` to run executables.
-/
def augmentedEnvVars (self : Workspace) : Array (String × Option String) :=
  self.env.installVars ++ #[
    ("LEAN_PATH", some self.augmentedLeanPath.toString),
    ("LEAN_SRC_PATH", some self.augmentedLeanSrcPath.toString),
    (sharedLibPathEnvVar, some self.augmentedSharedLibPath.toString)
  ]
