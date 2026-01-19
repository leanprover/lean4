/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Env
public import Lake.Config.LeanExe
public import Lake.Config.ExternLib
public import Lake.Config.FacetConfig
public import Lake.Config.TargetConfig
meta import all Lake.Util.OpaqueType

set_option doc.verso true

open System
open Lean (Name LeanOptions)

namespace Lake

/-- A Lake workspace -- the top-level package directory. -/
public structure Workspace : Type where
  /-- The root package of the workspace. -/
  root : Package
  /-- The detected {lean}`Lake.Env` of the workspace. -/
  lakeEnv : Lake.Env
  /-- The Lake cache. -/
  lakeCache : Cache :=
    if root.bootstrap then lakeEnv.lakeSystemCache?.getD ⟨root.lakeDir / "cache"⟩
    else lakeEnv.lakeCache?.getD ⟨root.lakeDir / "cache"⟩
  /--
  The CLI arguments Lake was run with.
  Used by {lit}`lake update` to perform a restart of Lake on a toolchain update.
  A value of {lean}`none` means that Lake is not restartable via the CLI.
  -/
  lakeArgs? : Option (Array String) := none
  /--
  The packages within the workspace
  (in {lit}`require` declaration order with the root coming first).
  -/
  packages : Array Package := {}
  /-- Name-package map of packages within the workspace. -/
  packageMap : DNameMap NPackage := {}
  /-- Configuration map of facets defined in the workspace. -/
  facetConfigs : DNameMap FacetConfig := {}

public instance : Nonempty Workspace :=
  have : Inhabited Package := Classical.inhabited_of_nonempty inferInstance
  ⟨by constructor <;> exact default⟩

public hydrate_opaque_type OpaqueWorkspace Workspace

/-- Returns the names of the root modules of the package's default targets. -/
public def Package.defaultTargetRoots (self : Package) : Array Lean.Name :=
  self.defaultTargets.flatMap fun target =>
    if let some lib := self.findLeanLib? target then
      lib.roots
    else if let some exe := self.findLeanExe? target then
      #[exe.root.name]
    else
      #[]

namespace Workspace

/-- **For internal use.** Whether this workspace is Lean itself.  -/
@[inline] def bootstrap (ws : Workspace) : Bool :=
  ws.root.bootstrap

/-- The path to the workspace's directory (i.e., the directory of the root package). -/
@[inline] public def dir (self : Workspace) : FilePath :=
  self.root.dir

/-- The workspace's configuration. -/
@[inline] public def config (self : Workspace) : WorkspaceConfig :=
  self.root.config.toWorkspaceConfig

/-- The path to the workspace' Lake directory relative to {lean}`dir`. -/
@[inline] public def relLakeDir (self : Workspace) : FilePath :=
  self.root.relLakeDir

/-- The full path to the workspace's Lake directory (e.g., {lit}`.lake`). -/
@[inline] public def lakeDir (self : Workspace) : FilePath :=
  self.root.lakeDir

/-- Whether the Lake artifact cache should be enabled by default for packages in the workspace. -/
public def enableArtifactCache (ws : Workspace) : Bool :=
  ws.lakeEnv.enableArtifactCache? <|> ws.root.enableArtifactCache? |>.getD false

/-- Whether the Lake artifact cache should is enabled for workspace's root package. -/
public def isRootArtifactCacheEnabled (ws : Workspace) : Bool :=
  ws.root.enableArtifactCache? <|> ws.lakeEnv.enableArtifactCache? |>.getD false

/-- The path to the workspace's remote packages directory relative to {lean}`dir`. -/
@[inline] public def relPkgsDir (self : Workspace) : FilePath :=
  self.root.relPkgsDir

/-- The workspace's {lean}`dir` joined with its {lean}`relPkgsDir`. -/
@[inline] public def pkgsDir (self : Workspace) : FilePath :=
  self.root.pkgsDir

/-- Arguments to pass to {lit}`lean` for files outside a library (e.g., via {lit}`lake lean`). -/
@[inline] public def leanArgs (self : Workspace) : Array String :=
  self.root.moreLeanArgs

/-- Options to pass to {lit}`lean` for files outside a library (e.g., via {lit}`lake lean`). -/
@[inline] public def leanOptions (self : Workspace) : LeanOptions :=
  self.root.leanOptions

/-- Options to pass to the Lean server when editing Lean files outside a library. -/
@[inline] public def serverOptions (self : Workspace) : LeanOptions :=
  self.root.moreServerOptions

/-- Returns the names of the root modules of the workpace root's default targets. -/
@[inline] public def defaultTargetRoots (self : Workspace) : Array Lean.Name :=
  self.root.defaultTargetRoots

/-- The workspace's Lake manifest. -/
@[inline] public def manifestFile (self : Workspace) : FilePath :=
  self.root.manifestFile

/-- The path to the workspace file used to configure automatic package overloads. -/
@[inline] public def packageOverridesFile (self : Workspace) : FilePath :=
  self.lakeDir / "package-overrides.json"

/-- Add a package to the workspace. -/
public def addPackage (pkg : Package) (self : Workspace) : Workspace :=
  {self with packages := self.packages.push pkg, packageMap := self.packageMap.insert pkg.keyName pkg}

/-- Returns the unique package in the workspace (if any) that is identified by  {lean}`keyName`. -/
@[inline] public protected def findPackageByKey? (keyName : Name) (self : Workspace) : Option (NPackage keyName) :=
  self.packageMap.get? keyName

/--
Returns the first package in the workspace (if any) that has been assigned the {lean}`name`.

This can be used to find the package corresponding to a user-provided name. If the package's unique
identifier is already available, use {name (full := Workspace.findPackageByKey?)}`findPackageByKey?`
instead.
-/
@[inline] public protected def findPackageByName? (name : Name) (self : Workspace) : Option Package :=
  self.packages.find? (·.baseName == name)

/--
**Deprecated.** If attempting to find the package corresponding to a user-provided name,
use {name (full := Workspace.findPackageByName?)}`findPackageByName?`. Otherwise, if the package's
unique identifier is available, use {name (full := Workspace.findPackageByKey?)}`findPackageByKey?`.
-/
@[deprecated "Use `findPackageByKey?` or `findPackageByName?` instead" (since := "2025-12-03")]
public protected abbrev findPackage? (name : Name) (self : Workspace) : Option (NPackage name) :=
  self.findPackageByKey? name

/-- Try to find a script in the workspace with the given name. -/
public protected def findScript? (script : Name) (self : Workspace) : Option Script :=
  self.packages.findSome? (·.scripts.find? script)

/-- Check if the module is local to any package in the workspace. -/
public def isLocalModule (mod : Name) (self : Workspace) : Bool :=
  self.packages.any fun pkg => pkg.isLocalModule mod

/-- Check if the module is buildable by any package in the workspace. -/
public def isBuildableModule (mod : Name) (self : Workspace) : Bool :=
  self.packages.any fun pkg => pkg.isBuildableModule mod

/-- Locate the named, buildable, importable, local module in the workspace. -/
public protected def findModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packages.findSome? (·.findModule? mod)

/-- For each package in the workspace, locate the named, buildable, importable, local module. -/
public protected def findModules (mod : Name) (self : Workspace) : Array Module :=
  self.packages.filterMap (·.findModule? mod)

/-- Locate the named, buildable, but not necessarily importable, module in the workspace. -/
public def findTargetModule? (mod : Name) (self : Workspace) : Option Module :=
  self.packages.findSome? (·.findTargetModule? mod)

/-- Returns the buildable module in the workspace whose source file is {lean}`path`.  -/
public def findModuleBySrc? (path : FilePath) (self : Workspace) : Option Module :=
  self.packages.findSome? (·.findModuleBySrc? path)

/-- Try to find a Lean library in the workspace with the given name. -/
public protected def findLeanLib? (name : Name) (self : Workspace) : Option LeanLib :=
  self.packages.findSome? fun pkg => pkg.findLeanLib? name

/-- Try to find a Lean executable in the workspace with the given name. -/
public protected def findLeanExe? (name : Name) (self : Workspace) : Option LeanExe :=
  self.packages.findSome? fun pkg => pkg.findLeanExe? name

/-- Try to find an external library in the workspace with the given name. -/
public protected def findExternLib? (name : Name) (self : Workspace) : Option ExternLib :=
  self.packages.findSome? fun pkg => pkg.findExternLib? name

/-- Try to find a target configuration in the workspace with the given name. -/
public def findTargetConfig? (name : Name) (self : Workspace) : Option ((pkg : Package) × TargetConfig pkg.keyName name) :=
  self.packages.findSome? fun pkg => pkg.findTargetConfig? name <&> (⟨pkg, ·⟩)

/-- Try to find a target declaration in the workspace with the given name.  -/
public def findTargetDecl? (name : Name) (self : Workspace) : Option ((pkg : Package) × NConfigDecl pkg.keyName name) :=
  self.packages.findSome? fun pkg => pkg.findTargetDecl? name <&> (⟨pkg, ·⟩)

/-- Add a facet to the workspace. -/
public def addFacetConfig {name} (cfg : FacetConfig name) (self : Workspace) : Workspace :=
  {self with facetConfigs := self.facetConfigs.insert name cfg}

/-- Try to find a facet configuration in the workspace with the given name. -/
public def findFacetConfig? (name : Name) (self : Workspace) : Option (FacetConfig name) :=
  self.facetConfigs.get? name

/-- Add a module facet to the workspace. -/
public def addModuleFacetConfig (cfg : ModuleFacetConfig name) (self : Workspace) : Workspace :=
  self.addFacetConfig cfg.toFacetConfig

/-- Try to find a module facet configuration in the workspace with the given name. -/
public def findModuleFacetConfig? (name : Name) (self : Workspace) : Option (ModuleFacetConfig name) :=
  self.findFacetConfig? name |>.bind (·.toKind? Module.facetKind)

/-- Add a package facet to the workspace. -/
public def addPackageFacetConfig (cfg : PackageFacetConfig name) (self : Workspace) : Workspace :=
  self.addFacetConfig cfg.toFacetConfig

/-- Try to find a package facet configuration in the workspace with the given name. -/
public def findPackageFacetConfig? (name : Name) (self : Workspace) : Option (PackageFacetConfig name) :=
  self.findFacetConfig? name |>.bind (·.toKind? Package.facetKind)

/-- Add a library facet to the workspace. -/
public def addLibraryFacetConfig (cfg : LibraryFacetConfig name) (self : Workspace) : Workspace :=
  self.addFacetConfig cfg.toFacetConfig

/-- Try to find a library facet configuration in the workspace with the given name. -/
public def findLibraryFacetConfig? (name : Name) (self : Workspace) : Option (LibraryFacetConfig name) :=
  self.findFacetConfig? name |>.bind (·.toKind? LeanLib.facetKind)

/-- The workspace's binary directories (which are added to {lit}`PATH`). -/
public def binPath (self : Workspace) : SearchPath :=
  self.packages.foldl (fun dirs pkg => pkg.binDir :: dirs) []

/-- The workspace's Lean library directories (which are added to {lit}`LEAN_PATH`). -/
public def leanPath (self : Workspace) : SearchPath :=
  self.packages.foldl (fun dirs pkg => pkg.leanLibDir :: dirs) []

/-- The workspace's source directories (which are added to {lit}`LEAN_SRC_PATH`). -/
public def leanSrcPath (self : Workspace) : SearchPath :=
  self.packages.foldl (init := {}) fun dirs pkg =>
    pkg.targetDecls.foldr (init := dirs) fun cfg dirs =>
      if let some cfg := cfg.leanLibConfig? then
        pkg.srcDir / cfg.srcDir :: dirs
      else
        dirs

/--
The workspace's shared library path (e.g., for {lit}`--load-dynlib`).
This is added to the {lean}`sharedLibPathEnvVar` by {lit}`lake env`.
-/
public def sharedLibPath (self : Workspace) : SearchPath :=
   self.packages.foldr (fun pkg dirs => pkg.sharedLibDir :: dirs) []

/--
The augmented {lit}`PATH` of the workspace environment.

This prepends the detected {lean}`self.lakeEnv.path` of the system environment with
the workspace's {lean}`binPath`. On Windows, it also adds the workspace's {lean}`sharedLibPath`.
-/
public def augmentedPath (self : Workspace) : SearchPath :=
  if Platform.isWindows then
    self.binPath ++ self.sharedLibPath ++ self.lakeEnv.path
  else
    self.binPath ++ self.lakeEnv.path

/--
The detected {lit}`LEAN_PATH` of the environment augmented with
the workspace's {lean}`leanPath` and Lake's {name (full := LakeInstall.libDir)}`libDir`.
-/
public def augmentedLeanPath (self : Workspace) : SearchPath :=
  self.leanPath ++ self.lakeEnv.leanPath

/--
The detected {lit}`LEAN_SRC_PATH` of the environment augmented with
the workspace's {lean}`leanSrcPath` and Lake's {name (full := LakeInstall.srcDir)}`srcDir`.
-/
public def augmentedLeanSrcPath (self : Workspace) : SearchPath :=
  self.leanSrcPath ++ self.lakeEnv.leanSrcPath

/-
The detected `sharedLibPathEnv` value of the environment augmented with
the workspace's `libPath` and Lean installation's shared library directories.

The order is Lean's, the workspace's, and then the environment's.
Lean's comes first because Lean needs to load its own shared libraries from this path.
Giving the workspace greater precedence can break this (e.g., when bootstrapping),
-/
public def augmentedSharedLibPath (self : Workspace) : SearchPath :=
  self.lakeEnv.lean.sharedLibPath ++ self.sharedLibPath ++ self.lakeEnv.initSharedLibPath

/--
The detected environment augmented with Lake's and the workspace's configuration.
These are the settings use by {lit}`lake env` / {name (scope := "Lake.CLI.Actions")}`Lake.env`
to run executables.
-/
public def augmentedEnvVars (self : Workspace) : Array (String × Option String) :=
  let vars := self.lakeEnv.baseVars ++ #[
    ("LAKE_CACHE_DIR", some self.lakeCache.dir.toString),
    ("LAKE_ARTIFACT_CACHE", toString self.enableArtifactCache),
    ("LEAN_PATH", some self.augmentedLeanPath.toString),
    ("LEAN_SRC_PATH", some self.augmentedLeanSrcPath.toString),
    -- Allow the Lean version to change dynamically within core
    ("LEAN_GITHASH", if self.bootstrap then none else some self.lakeEnv.leanGithash),
    ("PATH", some self.augmentedPath.toString)
  ]
  if Platform.isWindows then
    vars
  else
    vars.push (sharedLibPathEnvVar, some self.augmentedSharedLibPath.toString)

/-- Remove all packages' build outputs (i.e., delete their build directories). -/
public def clean (self : Workspace) : IO Unit := do
  self.packages.forM fun pkg => pkg.clean
