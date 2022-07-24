/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Config.Opaque
import Lake.Config.LeanLibConfig
import Lake.Config.LeanExeConfig
import Lake.Config.ExternLibConfig
import Lake.Config.WorkspaceConfig
import Lake.Config.Dependency
import Lake.Config.Script
import Lake.Util.DRBMap

open Std System Lean

namespace Lake

--------------------------------------------------------------------------------
/-! # Defaults -/
--------------------------------------------------------------------------------

/-- The default setting for a `PackageConfig`'s `buildDir` option. -/
def defaultBuildDir : FilePath := "build"

/-- The default setting for a `PackageConfig`'s `binDir` option. -/
def defaultBinDir : FilePath := "bin"

/-- The default setting for a `PackageConfig`'s `libDir` option. -/
def defaultLibDir : FilePath := "lib"

/-- The default setting for a `PackageConfig`'s `oleanDir` option. -/
def defaultOleanDir : FilePath := defaultLibDir

/-- The default setting for a `PackageConfig`'s `irDir` option. -/
def defaultIrDir : FilePath := "ir"

--------------------------------------------------------------------------------
/-! # PackageConfig -/
--------------------------------------------------------------------------------

/-- A `Package`'s declarative configuration. -/
structure PackageConfig extends WorkspaceConfig, LeanConfig where

  /-- The `Name` of the package. -/
  name : Name

  /--
  An extra `OpaqueTarget` that should be built before the package.

  `OpaqueTarget.collectList/collectArray` can be used combine multiple
  extra targets into a single `extraDepTarget`.

  **DEPRECATED:** Use separate custom `target` declarations instead?
  -/
  extraDepTarget : Option OpaqueTarget := none

  /--
  Whether to compile each of the package's module into a native shared library
  that is loaded whenever the module is imported. This speeds up evaluation of
  metaprograms and enables the interpreter to run functions marked `@[extern]`.

  Defaults to `false`.
  -/
  precompileModules : Bool := false

  /--
  Whether the package is "Lean-only". A Lean-only package does not produce
  native files for modules (e.g. `.c`, `.o`).

  Defaults to `false`. Setting `precompileModules` to `true` will override this
  setting and produce native files anyway (as they are needed to build module
  dynlibs).
  -/
  isLeanOnly : Bool := false

  /--
  Additional arguments to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake server`.
  -/
  moreServerArgs : Array String := #[]

  /--
  The directory containing the package's Lean source files.
  Defaults to the package's directory.

  (This will be passed to `lean` as the `-R` option.)
  -/
  srcDir : FilePath := "."

  /--
  The directory to which Lake should output the package's build results.
  Defaults to `defaultBuildDir` (i.e., `build`).
  -/
  buildDir : FilePath := defaultBuildDir

  /--
  The build subdirectory to which Lake should output the package's `.olean` files.
  Defaults to  `defaultOleanDir` (i.e., `lib`).
  -/
  oleanDir : FilePath := defaultOleanDir

  /--
  The build subdirectory to which Lake should output
  the package's intermediary results (e.g., `.c` and `.o` files).
  Defaults to `defaultIrDir` (i.e., `ir`).
  -/
  irDir : FilePath := defaultIrDir

  /--
  The build subdirectory to which Lake should output the package's static library.
  Defaults to `defaultLibDir` (i.e., `lib`).
  -/
  libDir : FilePath := defaultLibDir

  /--
  The build subdirectory to which Lake should output the package's binary executable.
  Defaults to `defaultBinDir` (i.e., `bin`).
  -/
  binDir : FilePath := defaultBinDir

deriving Inhabited

--------------------------------------------------------------------------------
/-! # Package -/
--------------------------------------------------------------------------------

abbrev DNameMap α := DRBMap Name α Lean.Name.quickCmp
@[inline] def DNameMap.empty : DNameMap α := DRBMap.empty

/-- A Lake package -- its location plus its configuration. -/
structure Package where
  /-- The path to the package's directory. -/
  dir : FilePath
  /-- The package's user-defined configuration. -/
  config : PackageConfig
  /-- The elaboration environment of the package's configuration file. -/
  configEnv : Environment
  /-- The Lean `Options` the package configuration was elaborated with. -/
  leanOpts : Options
  /-- (Opaque references to) the package's direct dependencies. -/
  opaqueDeps : Array OpaquePackage := #[]
  /-- Lean library configurations for the package. -/
  leanLibConfigs : NameMap LeanLibConfig := {}
  /-- Lean binary executable configurations for the package. -/
  leanExeConfigs : NameMap LeanExeConfig := {}
  /-- External library targets for the package. -/
  externLibConfigs : NameMap ExternLibConfig := {}
  /-- (Opaque references to) targets defined in the package. -/
  opaqueTargetConfigs : NameMap OpaqueTargetConfig := {}
  /--
  The names of the package's targets to build by default
  (i.e., on a bare `lake build` of the package).
  -/
  defaultTargets : Array Name := #[]
  /-- Scripts for the package. -/
  scripts : NameMap Script := {}
  deriving Inhabited

hydrate_opaque_type OpaquePackage Package

abbrev PackageSet := RBTree Package (·.config.name.quickCmp ·.config.name)
@[inline] def PackageSet.empty : PackageSet := RBTree.empty

namespace Package

/-- The package's name. -/
@[inline] def name (self : Package) : Name :=
  self.config.name

/-- An `Array` of the package's direct dependencies. -/
@[inline] def deps (self : Package) : Array Package  :=
  self.opaqueDeps.map (·.get)

/-- The package's `extraDepTarget` configuration. -/
@[inline] def extraDepTarget (self : Package) : OpaqueTarget :=
  self.config.extraDepTarget.getD Target.nil

/-- The package's `precompileModules` configuration. -/
@[inline] def precompileModules (self : Package) : Bool :=
  self.config.precompileModules

/-- The package's `isLeanOnly` configuration. -/
@[inline] def isLeanOnly (self : Package) : Bool :=
  self.config.isLeanOnly

/-- The package's `moreServerArgs` configuration. -/
@[inline] def moreServerArgs (self : Package) : Array String :=
  self.config.moreServerArgs

/-- The package's `dir` joined with its `srcDir` configuration. -/
@[inline] def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir

/-- The package's root directory for `lean` (i.e., `srcDir`). -/
@[inline] def rootDir (self : Package) : FilePath :=
  self.srcDir

/-- The package's `dir` joined with its `buildDir` configuration. -/
@[inline] def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir

/-- The package's `buildDir` joined with its `oleanDir` configuration. -/
@[inline] def oleanDir (self : Package) : FilePath :=
  self.buildDir / self.config.oleanDir

/-- The package's `buildType` configuration. -/
@[inline] def buildType (self : Package) : BuildType :=
  self.config.buildType

/-- The package's `moreLeanArgs` configuration. -/
@[inline] def moreLeanArgs (self : Package) : Array String :=
  self.config.moreLeanArgs

/-- The package's `moreLeancArgs` configuration. -/
@[inline] def moreLeancArgs (self : Package) : Array String :=
  self.config.moreLeancArgs

/-- The package's `moreLinkArgs` configuration. -/
@[inline] def moreLinkArgs (self : Package) : Array String :=
  self.config.moreLinkArgs

/-- The package's `buildDir` joined with its `irDir` configuration. -/
@[inline] def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir

/-- The package's `buildDir` joined with its `libDir` configuration. -/
@[inline] def libDir (self : Package) : FilePath :=
  self.buildDir / self.config.libDir

/-- The package's `buildDir` joined with its `binDir` configuration. -/
@[inline] def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir

/-- Whether the given module is considered local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun _ lib => lib.isLocalModule mod)

/-- Whether the given module is in the package (i.e., can build it). -/
def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun _ lib => lib.isBuildableModule mod) ||
  self.leanExeConfigs.any (fun _ exe => exe.root == mod)

/-- Remove the package's build outputs (i.e., delete its build directory). -/
def clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir
