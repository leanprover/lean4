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
import Lake.Load.Config
import Lake.Util.DRBMap
import Lake.Util.OrdHashSet
import Lake.Util.Platform

open System Lean

namespace Lake

/--
Platform-specific archive file with an optional name prefix
(i.e., `{name}-{platformDescriptor}.tar.gz`).
-/
def nameToArchive (name? : Option String) : String :=
  match name? with
  | none => s!"{platformDescriptor}.tar.gz"
  | some name => s!"{name}-{platformDescriptor}.tar.gz"

/--
First tries to convert a string into a legal name.
If that fails, defaults to making it a simple name (e.g., `Lean.Name.mkSimple`).
Currently used for package and target names taken from the CLI.
-/
def stringToLegalOrSimpleName (s : String) : Name :=
  if s.toName.isAnonymous then Lean.Name.mkSimple s else s.toName

--------------------------------------------------------------------------------
/-! # Defaults -/
--------------------------------------------------------------------------------

/-- The default setting for a `PackageConfig`'s `buildDir` option. -/
def defaultBuildDir : FilePath := "build"

/-- The default setting for a `PackageConfig`'s `leanLibDir` option. -/
def defaultLeanLibDir : FilePath := "lib"

/-- The default setting for a `PackageConfig`'s `nativeLibDir` option. -/
def defaultNativeLibDir : FilePath := "lib"

/-- The default setting for a `PackageConfig`'s `binDir` option. -/
def defaultBinDir : FilePath := "bin"

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
  **This field is deprecated.**

  The path of a package's manifest file, which stores the exact versions
  of its resolved dependencies.

  Defaults to `defaultManifestFile` (i.e., `lake-manifest.json`).
  -/
  manifestFile : Option FilePath := none

  /-- An `Array` of target names to build whenever the package is used. -/
  extraDepTargets : Array Name := #[]

  /--
  Whether to compile each of the package's module into a native shared library
  that is loaded whenever the module is imported. This speeds up evaluation of
  metaprograms and enables the interpreter to run functions marked `@[extern]`.

  Defaults to `false`.
  -/
  precompileModules : Bool := false

  /--
  **Deprecated in favor of `moreGlobalServerArgs`.**
  Additional arguments to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake serve`, both for this package and
  also for any packages browsed from this one in the same session.
  -/
  moreServerArgs : Array String := #[]

  /--
  Additional arguments to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake serve`, both for this package and
  also for any packages browsed from this one in the same session.
  -/
  moreGlobalServerArgs : Array String := moreServerArgs

  /--
  The directory containing the package's Lean source files.
  Defaults to the package's directory.

  (This will be passed to `lean` as the `-R` option.)
  -/
  srcDir : FilePath := "."

  /--
  The directory to which Lake should output the package's build results.
  Defaults to `defaultLakeDir / defaultBuildDir` (i.e., `.lake/build`).
  -/
  buildDir : FilePath := defaultLakeDir / defaultBuildDir

  /--
  The build subdirectory to which Lake should output the package's
  binary Lean libraries (e.g., `.olean`, `.ilean` files).
  Defaults to  `defaultLeanLibDir` (i.e., `lib`).
  -/
  leanLibDir : FilePath := defaultLeanLibDir

  /--
  The build subdirectory to which Lake should output the package's
  native libraries (e.g., `.a`, `.so`, `.dll` files).
  Defaults to `defaultNativeLibDir` (i.e., `lib`).
  -/
  nativeLibDir : FilePath := defaultNativeLibDir

  /--
  The build subdirectory to which Lake should output the package's binary executable.
  Defaults to `defaultBinDir` (i.e., `bin`).
  -/
  binDir : FilePath := defaultBinDir

  /--
  The build subdirectory to which Lake should output
  the package's intermediary results (e.g., `.c` and `.o` files).
  Defaults to `defaultIrDir` (i.e., `ir`).
  -/
  irDir : FilePath := defaultIrDir

  /--
  The URL of the GitHub repository to upload and download releases of this package.
  If `none` (the default), for downloads, Lake uses the URL the package was download
  from (if it is a dependency) and for uploads, uses `gh`'s default.
  -/
  releaseRepo? : Option String := none

  /--
  The name of the build archive on GitHub. Defaults to `none`.
  The archive's full file name will be `nameToArchive buildArchive?`.
  -/
  buildArchive? : Option String := none

  /--
  Whether to prefer downloading a prebuilt release (from GitHub) rather than
  building this package from the source when this package is used as a dependency.
  -/
  preferReleaseBuild : Bool := false

deriving Inhabited

--------------------------------------------------------------------------------
/-! # Package -/
--------------------------------------------------------------------------------


declare_opaque_type OpaquePostUpdateHook (pkg : Name)

/-- A Lake package -- its location plus its configuration. -/
structure Package where
  /-- The path to the package's directory. -/
  dir : FilePath
  /-- The path to the package's directory relative to the workspace. -/
  relDir : FilePath
  /-- The package's user-defined configuration. -/
  config : PackageConfig
  /-- The elaboration environment of the package's configuration file. -/
  configEnv : Environment
  /-- The Lean `Options` the package configuration was elaborated with. -/
  leanOpts : Options
  /-- The path to the package's configuration file. -/
  configFile : FilePath
  /-- The path to the package's JSON manifest of remote dependencies (relative to `dir`). -/
  relManifestFile : FilePath := config.manifestFile.getD defaultManifestFile
  /-- The URL to this package's Git remote. -/
  remoteUrl? : Option String := none
  /-- (Opaque references to) the package's direct dependencies. -/
  opaqueDeps : Array OpaquePackage := #[]
  /-- Lean library configurations for the package. -/
  leanLibConfigs : OrdNameMap LeanLibConfig := {}
  /-- Lean binary executable configurations for the package. -/
  leanExeConfigs : OrdNameMap LeanExeConfig := {}
  /-- External library targets for the package. -/
  externLibConfigs : DNameMap (ExternLibConfig config.name) := {}
  /-- (Opaque references to) targets defined in the package. -/
  opaqueTargetConfigs : DNameMap (OpaqueTargetConfig config.name) := {}
  /--
  The names of the package's targets to build by default
  (i.e., on a bare `lake build` of the package).
  -/
  defaultTargets : Array Name := #[]
  /-- Scripts for the package. -/
  scripts : NameMap Script := {}
  /--
  The names of the package's scripts run by default
  (i.e., on a bare `lake run` of the package).
  -/
  defaultScripts : Array Script := #[]
  /-- Post-`lake update` hooks for the package. -/
  postUpdateHooks : Array (OpaquePostUpdateHook config.name) := #[]

instance : Nonempty Package :=
  have : Inhabited Environment := Classical.inhabited_of_nonempty inferInstance
  by refine' ⟨{..}⟩ <;> exact default

hydrate_opaque_type OpaquePackage Package

instance : Hashable Package where hash pkg := hash pkg.config.name
instance : BEq Package where beq p1 p2 := p1.config.name == p2.config.name

abbrev PackageSet := HashSet Package
@[inline] def PackageSet.empty : PackageSet := HashSet.empty

abbrev OrdPackageSet := OrdHashSet Package
@[inline] def OrdPackageSet.empty : OrdPackageSet := OrdHashSet.empty

/-- The package's name. -/
abbrev Package.name (self : Package) : Name :=
  self.config.name

/-- A package with a name known at type-level. -/
structure NPackage (name : Name) extends Package where
  name_eq : toPackage.name = name

attribute [simp] NPackage.name_eq

instance : CoeOut (NPackage name) Package := ⟨NPackage.toPackage⟩
instance : CoeDep Package pkg (NPackage pkg.name) := ⟨⟨pkg, rfl⟩⟩

/-- The package's name. -/
abbrev NPackage.name (_ : NPackage n) := n

/--
The type of a post-update hooks monad.
`IO` equipped with logging ability and information about the Lake configuration.
-/
abbrev PostUpdateFn (pkgName : Name) := NPackage pkgName → LakeT LogIO PUnit

structure PostUpdateHook (pkgName : Name) where
  fn : PostUpdateFn pkgName
  deriving Inhabited

hydrate_opaque_type OpaquePostUpdateHook PostUpdateHook name

structure PostUpdateHookDecl where
  pkg : Name
  fn : PostUpdateFn pkg

namespace Package

/-- The package's direct dependencies. -/
@[inline] def deps (self : Package) : Array Package  :=
  self.opaqueDeps.map (·.get)

/-- The path to the package's Lake directory relative to `dir` (e.g., `.lake`). -/
@[inline] def relLakeDir (_ : Package) : FilePath :=
  defaultLakeDir

/-- The full path to the package's Lake directory (i.e, `dir` joined with `relLakeDir`). -/
@[inline] def lakeDir (self : Package) : FilePath :=
  self.dir / self.relLakeDir

/-- The path for storing the package's remote dependencies relative to `dir` (i.e., `packagesDir`). -/
@[inline] def relPkgsDir (self : Package) : FilePath :=
  self.config.packagesDir

/-- The package's `dir` joined with its `relPkgsDir`. -/
@[inline] def pkgsDir (self : Package) : FilePath :=
  self.dir / self.relPkgsDir

/-- The path to the package's JSON manifest of remote dependencies. -/
@[inline] def manifestFile (self : Package) : FilePath :=
  self.dir / self.relManifestFile

/-- The package's `dir` joined with its `buildDir` configuration. -/
@[inline] def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir

/-- The package's `extraDepTargets` configuration. -/
@[inline] def extraDepTargets (self : Package) : Array Name :=
  self.config.extraDepTargets

/-- The package's `releaseRepo?` configuration. -/
@[inline] def releaseRepo? (self : Package) : Option String :=
  self.config.releaseRepo?

/-- The package's `buildArchive?` configuration. -/
@[inline] def buildArchive? (self : Package) : Option String :=
  self.config.buildArchive?

/-- The file name of the package's build archive derived from `buildArchive?`. -/
@[inline] def buildArchive (self : Package) : String :=
  nameToArchive self.buildArchive?

/-- The package's `lakeDir` joined with its `buildArchive` configuration. -/
@[inline] def buildArchiveFile (self : Package) : FilePath :=
  self.lakeDir / self.buildArchive

/-- The package's `preferReleaseBuild` configuration. -/
@[inline] def preferReleaseBuild (self : Package) : Bool :=
  self.config.preferReleaseBuild

/-- The package's `precompileModules` configuration. -/
@[inline] def precompileModules (self : Package) : Bool :=
  self.config.precompileModules

/-- The package's `moreGlobalServerArgs` configuration. -/
@[inline] def moreGlobalServerArgs (self : Package) : Array String :=
  self.config.moreGlobalServerArgs

/-- The package's `moreServerOptions` configuration appended to its `leanOptions` configuration. -/
@[inline] def moreServerOptions (self : Package) : Array LeanOption :=
  self.config.leanOptions ++ self.config.moreServerOptions

/-- The package's `buildType` configuration. -/
@[inline] def buildType (self : Package) : BuildType :=
  self.config.buildType

/-- The package's `backend` configuration. -/
@[inline] def backend (self : Package) : Backend :=
  self.config.backend

/-- The package's `leanOptions` configuration. -/
@[inline] def leanOptions (self : Package) : Array LeanOption :=
  self.config.leanOptions

/-- The package's `moreLeanArgs` configuration appended to its `leanOptions` configuration. -/
@[inline] def moreLeanArgs (self : Package) : Array String :=
  self.config.leanOptions.map (·.asCliArg) ++ self.config.moreLeanArgs

/-- The package's `weakLeanArgs` configuration. -/
@[inline] def weakLeanArgs (self : Package) : Array String :=
  self.config.weakLeanArgs

/-- The package's `moreLeancArgs` configuration. -/
@[inline] def moreLeancArgs (self : Package) : Array String :=
  self.config.moreLeancArgs

/-- The package's `weakLeancArgs` configuration. -/
@[inline] def weakLeancArgs (self : Package) : Array String :=
  self.config.weakLeancArgs

/-- The package's `moreLinkArgs` configuration. -/
@[inline] def moreLinkArgs (self : Package) : Array String :=
  self.config.moreLinkArgs

/-- The package's `weakLinkArgs` configuration. -/
@[inline] def weakLinkArgs (self : Package) : Array String :=
  self.config.weakLinkArgs

/-- The package's `dir` joined with its `srcDir` configuration. -/
@[inline] def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir

/-- The package's root directory for `lean` (i.e., `srcDir`). -/
@[inline] def rootDir (self : Package) : FilePath :=
  self.srcDir

/-- The package's `buildDir` joined with its `leanLibDir` configuration. -/
@[inline] def leanLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.leanLibDir

/-- The package's `buildDir` joined with its `nativeLibDir` configuration. -/
@[inline] def nativeLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.nativeLibDir

/-- The package's `buildDir` joined with its `binDir` configuration. -/
@[inline] def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir

/-- The package's `buildDir` joined with its `irDir` configuration. -/
@[inline] def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir

/-- Whether the given module is considered local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun lib => lib.isLocalModule mod)

/-- Whether the given module is in the package (i.e., can build it). -/
def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun lib => lib.isBuildableModule mod) ||
  self.leanExeConfigs.any (fun exe => exe.root == mod)

/-- Remove the package's build outputs (i.e., delete its build directory). -/
def clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir
