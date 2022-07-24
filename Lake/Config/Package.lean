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

/-- The default setting for a `PackageConfig`'s `binRoot` option. -/
def defaultBinRoot : Name := `Main

--------------------------------------------------------------------------------
/-! # PackageFacet -/
--------------------------------------------------------------------------------

/-- A buildable component of a `Package`. -/
inductive PackageFacet
| /-- The package's binary executable. -/ exe
| /-- The package's static library. -/ staticLib
| /-- The package's shared library. -/ sharedLib
| /-- The package's lean library (e.g. `olean` / `ilean` files). -/ leanLib
| /-- The package has no buildable component. -/ none
deriving BEq, DecidableEq, Repr
instance : Inhabited PackageFacet := ⟨PackageFacet.exe⟩

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
  The optional `PackageFacet` to build on a bare `lake build` of the package.
  Can be one of `exe`, `leanLib`, `staticLib`, `sharedLib`, or `none`.
  Defaults to `exe`. See `lake help build` for more info on build facets.

  **DEPRECATED:**
  Package facets will be removed in a future version of Lake.
  Use a separate `lean_lib` or `lean_exe` default target instead.
  -/
  defaultFacet : PackageFacet := .exe

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
  The root module(s) of the package's library.

  Submodules of these roots (e.g., `Pkg.Foo` of `Pkg`) are considered
  part of the package.

  Defaults to a single root of the package's upper camel case `name`.
  -/
  libRoots : Array Name := #[toUpperCamelCase name]

  /--
  An `Array` of module `Glob`s to build for the package's library.
  Defaults to a `Glob.one` of each of the module's `libRoots`.

  Submodule globs build every source file within their directory.
  Local imports of glob'ed files (i.e., fellow modules of the package) are
  also recursively built.
  -/
  libGlobs : Array Glob := libRoots.map Glob.one

  /--
  The build subdirectory to which Lake should output
  the package's intermediary results (e.g., `.c` and `.o` files).
  Defaults to `defaultIrDir` (i.e., `ir`).
  -/
  irDir : FilePath := defaultIrDir

  /--
  The name of the package's static library.
  Defaults to the package's upper camel case `name`.
  -/
  libName : String := toUpperCamelCase name |>.toString (escape := false)

  /--
  The build subdirectory to which Lake should output the package's static library.
  Defaults to `defaultLibDir` (i.e., `lib`).
  -/
  libDir : FilePath := defaultLibDir

  /--
  The name of the package's binary executable.
  Defaults to the package's `name` with any `.` replaced with a `-`.
  -/
  binName : String := name.toStringWithSep "-" (escape := false)

  /--
  The build subdirectory to which Lake should output the package's binary executable.
  Defaults to `defaultBinDir` (i.e., `bin`).
  -/
  binDir : FilePath := defaultBinDir

  /--
  The root module of the package's binary executable.
  Defaults to `defaultBinRoot` (i.e., `Main`).

  The root is built by recursively building its
  local imports (i.e., fellow modules of the workspace).

  This setting is most useful for packages that are distributing both a
  library and a binary (like Lake itself). In such cases, it is common for
  there to be code (e.g., `main`) that is needed for the binary but should
  not be included in the library proper.
  -/
  binRoot : Name := defaultBinRoot

  /--
  Additional library `FileTarget`s (beyond the package's and its dependencies'
  Lean libraries) to build and link to the package's binaries (and to dependent
  packages' binaries).

  **DEPRECATED:** Use separate `extern_lib` targets instead.
  -/
  moreLibTargets : Array FileTarget := #[]

  /--
  Whether to expose symbols within the executable to the Lean interpreter.
  This allows the executable to interpret Lean files (e.g.,  via
  `Lean.Elab.runFrontend`).

  Implementation-wise, this passes `-rdynamic` to the linker when building
  on non-Windows systems.

  Defaults to `false`.
  -/
  supportInterpreter : Bool := false

deriving Inhabited

namespace PackageConfig

/-- The configuration of the package's library. -/
def toLeanLibConfig (self : PackageConfig) : LeanLibConfig where
  name := self.libName
  roots := self.libRoots
  globs := self.libGlobs
  toLeanConfig := self.toLeanConfig

/-- The configuration of the package's binary executable. -/
def toLeanExeConfig (self : PackageConfig) : LeanExeConfig where
  root := self.binRoot
  name := self.binName
  supportInterpreter := self.supportInterpreter
  toLeanConfig := self.toLeanConfig

end PackageConfig

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

/-- The package's `defaultFacet` configuration. -/
@[inline] def defaultFacet (self : Package) : PackageFacet :=
   self.config.defaultFacet

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

/-- The library configuration built into the package configuration. -/
@[inline] def builtinLibConfig (self : Package) : LeanLibConfig :=
  self.config.toLeanLibConfig

/-- The binary executable configuration built into the package configuration. -/
@[inline] def builtinExeConfig (self : Package) : LeanExeConfig :=
  self.config.toLeanExeConfig

/-- Whether the given module is considered local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun _ lib => lib.isLocalModule mod) ||
  self.builtinLibConfig.isLocalModule mod

/-- Whether the given module is in the package (i.e., can build it). -/
def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun _ lib => lib.isBuildableModule mod) ||
  self.leanExeConfigs.any (fun _ exe => exe.root == mod) ||
  self.builtinLibConfig.isBuildableModule mod ||
  self.config.binRoot == mod

/-- Remove the package's build outputs (i.e., delete its build directory). -/
def clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir
