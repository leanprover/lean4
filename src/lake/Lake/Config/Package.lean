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
import Lake.Util.OrdHashSet

open System Lean

namespace Lake

/-- A string descriptor of the `System.Platform` OS (`windows`, `macOS`, or `linux`). -/
def osDescriptor : String :=
  if Platform.isWindows then
    "windows"
  else if Platform.isOSX then
    "macOS"
  else
    "linux"

/--
A `tar.gz` file name suffix encoding the the current Platform.
(i.e, `osDescriptor` joined with `System.Platform.numBits`).
-/
def archiveSuffix :=
  s!"{osDescriptor}-{Platform.numBits}.tar.gz"

/-- If `name?`, `{name}-{archiveSuffix}`, otherwise just `archiveSuffix`. -/
def nameToArchive (name? : Option String) : String :=
  match name? with
  | none => archiveSuffix
  | some name => s!"{name}-{archiveSuffix}"

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

/-- The default setting for a `PackageConfig`'s `manifestFile` option. -/
def defaultManifestFile := "lake-manifest.json"

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
  The path of a package's manifest file, which stores the exact versions
  of its resolved dependencies.

  Defaults to `defaultManifestFile` (i.e., `lake-manifest.json`).
  -/
  manifestFile := defaultManifestFile

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

abbrev DNameMap α := DRBMap Name α Name.quickCmp
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
  /-- The URL to this package's Git remote. -/
  remoteUrl? : Option String := none
  /-- The Git tag of this package. -/
  gitTag? : Option String := none
  /-- (Opaque references to) the package's direct dependencies. -/
  opaqueDeps : Array OpaquePackage := #[]
  /-- Lean library configurations for the package. -/
  leanLibConfigs : NameMap LeanLibConfig := {}
  /-- Lean binary executable configurations for the package. -/
  leanExeConfigs : NameMap LeanExeConfig := {}
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

namespace Package

/-- The package's direct dependencies. -/
@[inline] def deps (self : Package) : Array Package  :=
  self.opaqueDeps.map (·.get)

/--
The path for storing the package's remote dependencies relative to `dir`.
Either its `packagesDir` configuration or `defaultPackagesDir`.
-/
def relPkgsDir (self : Package) : FilePath :=
  self.config.packagesDir.getD defaultPackagesDir

/-- The package's `dir` joined with its `relPkgsDir` -/
def pkgsDir (self : Package) : FilePath :=
  self.dir / self.relPkgsDir

/-- The package's JSON manifest of remote dependencies. -/
def manifestFile (self : Package) : FilePath :=
  self.dir / self.config.manifestFile

/-- The package's `dir` joined with its `buildDir` configuration. -/
@[inline] def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir

/-- The package's `extraDepTargets` configuration. -/
@[inline] def extraDepTargets (self : Package) : Array Name :=
  self.config.extraDepTargets

/-- The package's `releaseRepo?` configuration. -/
@[inline] def releaseRepo? (self : Package) : Option String :=
  self.config.releaseRepo?

/--
The package's URL × tag release.
Tries `releaseRepo?` first and then falls back to `remoteUrl?`.
-/
def release? (self : Package) : Option (String × String) := do
  let url ← self.releaseRepo? <|> self.remoteUrl?
  let tag ← self.gitTag?
  return (url, tag)

/-- The package's `buildArchive?` configuration. -/
@[inline] def buildArchive? (self : Package) : Option String :=
  self.config.buildArchive?

/-- The file name of the package's build archive derived from `buildArchive?`. -/
@[inline] def buildArchive (self : Package) : String :=
  nameToArchive self.buildArchive?

/-- The package's `buildDir` joined with its `buildArchive` configuration. -/
@[inline] def buildArchiveFile (self : Package) : FilePath :=
  self.buildDir / self.buildArchive

/-- The package's `preferReleaseBuild` configuration. -/
@[inline] def preferReleaseBuild (self : Package) : Bool :=
  self.config.preferReleaseBuild

/-- The package's `precompileModules` configuration. -/
@[inline] def precompileModules (self : Package) : Bool :=
  self.config.precompileModules

/-- The package's `moreServerArgs` configuration. -/
@[inline] def moreServerArgs (self : Package) : Array String :=
  self.config.moreServerArgs

/-- The package's `buildType` configuration. -/
@[inline] def buildType (self : Package) : BuildType :=
  self.config.buildType

/-- The package's `moreLeanArgs` configuration. -/
@[inline] def moreLeanArgs (self : Package) : Array String :=
  self.config.moreLeanArgs

/-- The package's `weakLeanArgs` configuration. -/
@[inline] def weakLeanArgs (self : Package) : Array String :=
  self.config.weakLeanArgs

/-- The package's `moreLeancArgs` configuration. -/
@[inline] def moreLeancArgs (self : Package) : Array String :=
  self.config.moreLeancArgs

/-- The package's `moreLinkArgs` configuration. -/
@[inline] def moreLinkArgs (self : Package) : Array String :=
  self.config.moreLinkArgs

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
  self.leanLibConfigs.any (fun _ lib => lib.isLocalModule mod)

/-- Whether the given module is in the package (i.e., can build it). -/
def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.leanLibConfigs.any (fun _ lib => lib.isBuildableModule mod) ||
  self.leanExeConfigs.any (fun _ exe => exe.root == mod)

/-- Remove the package's build outputs (i.e., delete its build directory). -/
def clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir
