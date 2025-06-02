/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
prelude
import Lake.Config.Defaults
import Lake.Config.OutFormat
import Lake.Config.WorkspaceConfig
import Lake.Config.Dependency
import Lake.Config.ConfigDecl
import Lake.Config.Script
import Lake.Load.Config
import Lake.Util.DRBMap
import Lake.Util.OrdHashSet
import Lake.Util.Version
import Lake.Util.FilePath

open System Lean

namespace Lake

/-- The default `buildArchive` configuration for a package with `name`. -/
@[inline] def defaultBuildArchive (name : Name) : String :=
  s!"{name.toString false}-{System.Platform.target}.tar.gz"

--------------------------------------------------------------------------------
/-! # PackageConfig -/
--------------------------------------------------------------------------------

set_option linter.unusedVariables false in
/-- A `Package`'s declarative configuration. -/
configuration PackageConfig (name : Name) extends WorkspaceConfig, LeanConfig where
  /-- **For internal use.** Whether this package is Lean itself. -/
  bootstrap : Bool := false

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
  Additional arguments to pass to the Lean language server
  (i.e., `lean --server`) launched by `lake serve`, both for this package and
  also for any packages browsed from this one in the same session.
  -/
  moreGlobalServerArgs, moreServerArgs : Array String := #[]

  /--
  The directory containing the package's Lean source files.
  Defaults to the package's directory.

  (This will be passed to `lean` as the `-R` option.)
  -/
  srcDir : FilePath := "."

  /--
  The directory to which Lake should output the package's build results.
  Defaults to `defaultBuildDir` (i.e., `.lake/build`).
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
  releaseRepo, releaseRepo? : Option String := none

  /--
  A custom name for the build archive for the GitHub cloud release.
  If `none` (the default), Lake defaults to `{(pkg-)name}-{System.Platform.target}.tar.gz`.
  -/
  buildArchive, buildArchive? : Option String := none

  /--
  Whether to prefer downloading a prebuilt release (from GitHub) rather than
  building this package from the source when this package is used as a dependency.
  -/
  preferReleaseBuild : Bool := false

  /--
  The name of the script, executable, or library by `lake test` when
  this package is the workspace root. To point to a definition in another
  package, use the syntax `<pkg>/<def>`.

  A script driver will be run by `lake test` with the arguments
  configured in `testDriverArgs`  followed by any specified on the CLI
  (e.g., via  `lake lint -- <args>...`). An executable driver will be built
  and then run like a script. A library will just be built.
  -/
  testDriver, testRunner : String := ""

  /--
  Arguments to pass to the package's test driver.
  These arguments will come before those passed on the command line via
  `lake test -- <args>...`.
  -/
  testDriverArgs : Array String := #[]

  /--
  The name of the script or executable used by `lake lint` when this package
  is the workspace root. To point to a definition in another package, use the
  syntax `<pkg>/<def>`.

  A script driver will be run by `lake lint` with the arguments
  configured in `lintDriverArgs` followed by any specified on the CLI
  (e.g., via  `lake lint -- <args>...`). An executable driver will be built
  and then run like a script.
  -/
  lintDriver : String := ""

  /--
  Arguments to pass to the package's linter.
  These arguments will come before those passed on the command line via
  `lake lint -- <args>...`.
  -/
  lintDriverArgs : Array String := #[]

  /--
  The package version. Versions have the form:

  ```
  v!"<major>.<minor>.<patch>[-<specialDescr>]"
  ```

  A version with a `-` suffix is considered a "prerelease".

  Lake suggest the following guidelines for incrementing versions:

  * **Major version increment** *(e.g., v1.3.0 → v2.0.0)*
    Indicates significant breaking changes in the package.
    Package users are not expected to update to the new version
    without manual intervention.

  * **Minor version increment** *(e.g., v1.3.0 → v1.4.0)*
    Denotes notable changes that are expected to be
    generally backwards compatible.
    Package users are expected to update to this version automatically
    and should be able to fix any breakages and/or warnings easily.

  * **Patch version increment** *(e.g., v1.3.0 → v1.3.1)*
    Reserved for bug fixes and small touchups.
    Package users are expected to update automatically and should not expect
    significant breakage, except in the edge case of users relying on the
    behavior of patched bugs.

  **Note that backwards-incompatible changes may occur at any version increment.**
  The is because the current nature of Lean (e.g., transitive imports,
  rich metaprogramming, reducibility in proofs), makes it infeasible to
  define a completely stable interface for a package.
  Instead, the different version levels indicate a change's intended significance
  and how difficult migration is expected to be.

  Versions of form the `0.x.x` are considered development versions prior to
  first official release. Like prerelease, they are not expected to closely
  follow the above guidelines.

  Packages without a defined version default to `0.0.0`.
  -/
  version : StdVer := {}

  /--
  Git tags of this package's repository that should be treated as versions.
  Package indices (e.g., Reservoir) can make use of this information to determine
  the Git revisions corresponding to released versions.

  Defaults to tags that are "version-like".
  That is, start with a `v` followed by a digit.
  -/
  versionTags : StrPat := defaultVersionTags

  /-- A short description for the package (e.g., for Reservoir). -/
  description : String := ""

  /--
  Custom keywords associated with the package.
  Reservoir can make use of a package's keywords to group related packages
  together and make it easier for users to discover them.

  Good keywords include the domain (e.g., `math`, `software-verification`,
  `devtool`), specific subtopics (e.g., `topology`,  `cryptology`), and
  significant implementation details (e.g., `dsl`, `ffi`, `cli`).
  For instance, Lake's keywords could be `devtool`, `cli`, `dsl`,
  `package-manager`, and `build-system`.
  -/
  keywords : Array String := #[]

  /--
  A URL to information about the package.

  Reservoir will already include a link to the package's GitHub repository
  (if the package is sourced from there). Thus, users are advised to specify
  something else for this (if anything).
  -/
  homepage : String := ""

  /--
  The package's license (if one).
  Should be a valid [SPDX License Expression][1].

  Reservoir requires that packages uses an OSI-approved license to be
  included in its index, and currently only supports single identifier
  SPDX expressions. For, a list of OSI-approved SPDX license identifiers,
  see the [SPDX LIcense List][2].

  [1]: https://spdx.github.io/spdx-spec/v3.0/annexes/SPDX-license-expressions/
  [2]: https://spdx.org/licenses/
  -/
  license : String := ""

  /--
  Files containing licensing information for the package.

  These should be the license files that users are expected to include when
  distributing package sources, which may be more then one file for some licenses.
  For example, the Apache 2.0 license requires the reproduction of a `NOTICE`
  file along with the license (if such a file exists).

  Defaults to `#["LICENSE"]`.
  -/
  licenseFiles : Array FilePath := #["LICENSE"]

  /--
  The path to the package's README.

  A README should be a Markdown file containing an overview of the package.
  Reservoir displays the rendered HTML of this file on a package's page.
  A nonstandard location can be used to provide a different README for Reservoir
  and GitHub.

  Defaults to `README.md`.
  -/
  readmeFile : FilePath := "README.md"

  /--
  Whether Reservoir should include the package in its index.
  When set to `false`, Reservoir will not add the package to its index
  and will remove it if it was already there (when Reservoir is next updated).
  -/
  reservoir : Bool := true

deriving Inhabited

instance : EmptyCollection (PackageConfig n) := ⟨{}⟩

/-- The package's name. -/
abbrev PackageConfig.name (_ : PackageConfig n) := n

/-- A package declaration from a configuration written in Lean. -/
structure PackageDecl where
  name : Name
  config : PackageConfig name
  deriving TypeName

--------------------------------------------------------------------------------
/-! # Package -/
--------------------------------------------------------------------------------

declare_opaque_type OpaquePostUpdateHook (pkg : Name)

/-- A Lake package -- its location plus its configuration. -/
structure Package where
  /-- The name of the package. -/
  name : Name
  /-- The absolute path to the package's directory. -/
  dir : FilePath
  /-- The path to the package's directory relative to the workspace. -/
  relDir : FilePath
  /-- The package's user-defined configuration. -/
  config : PackageConfig name
  /-- The absolute path to the package's configuration file. -/
  configFile : FilePath
  /-- The path to the package's configuration file (relative to `dir`). -/
  relConfigFile : FilePath
  /-- The path to the package's JSON manifest of remote dependencies (relative to `dir`). -/
  relManifestFile : FilePath := config.manifestFile.getD defaultManifestFile |>.normalize
  /-- The package's scope (e.g., in Reservoir). -/
  scope : String
  /-- The URL to this package's Git remote. -/
  remoteUrl : String
  /-- Dependency configurations for the package. -/
  depConfigs : Array Dependency := #[]
  /-- Target configurations in the order declared by the package. -/
  targetDecls : Array (PConfigDecl name) := #[]
  /-- Name-declaration map of target configurations in the package. -/
  targetDeclMap : DNameMap (NConfigDecl name) :=
    targetDecls.foldl (fun m d => m.insert d.name (.mk d rfl)) {}
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
  postUpdateHooks : Array (OpaquePostUpdateHook name) := #[]
  /-- The package's `buildArchive`/`buildArchive?` configuration. -/
  buildArchive : String :=
    if let some n := config.buildArchive then n else defaultBuildArchive name
  /-- The driver used for `lake test` when this package is the workspace root. -/
  testDriver : String := config.testDriver
  /-- The driver used for `lake lint` when this package is the workspace root. -/
  lintDriver : String := config.lintDriver

instance : Nonempty Package :=
  have : Inhabited Environment := Classical.inhabited_of_nonempty inferInstance
  ⟨by constructor <;> exact default⟩

instance : Hashable Package where hash pkg := hash pkg.name
instance : BEq Package where beq p1 p2 := p1.name == p2.name

abbrev PackageSet := Std.HashSet Package
@[inline] def PackageSet.empty : PackageSet := ∅

abbrev OrdPackageSet := OrdHashSet Package
@[inline] def OrdPackageSet.empty : OrdPackageSet := OrdHashSet.empty

instance : ToText Package := ⟨(·.name.toString)⟩
instance : ToJson Package := ⟨(toJson ·.name)⟩

/-- A package with a name known at type-level. -/
structure NPackage (n : Name) extends Package where
  name_eq : toPackage.name = n

attribute [simp] NPackage.name_eq

instance : CoeOut (NPackage n) Package := ⟨NPackage.toPackage⟩
instance : CoeDep Package pkg (NPackage pkg.name) := ⟨⟨pkg, rfl⟩⟩

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
  deriving TypeName

namespace Package

/-- **For internal use.** Whether this package is Lean itself.  -/
@[inline] def bootstrap (self : Package) : Bool  :=
  self.config.bootstrap

/-- The package version. -/
@[inline] def version (self : Package) : LeanVer  :=
  self.config.version

/-- The package's `versionTags` configuration. -/
@[inline] def versionTags (self : Package) : StrPat  :=
  self.config.versionTags

/-- The package's `description` configuration. -/
@[inline] def description (self : Package) : String  :=
  self.config.description

/-- The package's `keywords` configuration. -/
@[inline] def keywords (self : Package) : Array String  :=
  self.config.keywords

/-- The package's `homepage` configuration. -/
@[inline] def homepage (self : Package) : String  :=
  self.config.homepage

/-- The package's `reservoir` configuration. -/
@[inline] def reservoir (self : Package) : Bool  :=
  self.config.reservoir

/-- The package's `license` configuration. -/
@[inline] def license (self : Package) : String  :=
  self.config.license

/-- The package's `licenseFiles` configuration. -/
@[inline] def relLicenseFiles (self : Package) : Array FilePath :=
  self.config.licenseFiles.map (·.normalize)

/-- The package's `dir` joined with each of its `relLicenseFiles`. -/
@[inline] def licenseFiles (self : Package) : Array FilePath  :=
  self.relLicenseFiles.map (self.dir / ·.normalize)

/-- The package's `readmeFile` configuration. -/
@[inline] def relReadmeFile (self : Package) : FilePath  :=
  self.config.readmeFile.normalize

/-- The package's `dir` joined with its `relReadmeFile`. -/
@[inline] def readmeFile (self : Package) : FilePath  :=
  self.dir / self.relReadmeFile

/-- The path to the package's Lake directory relative to `dir` (e.g., `.lake`). -/
@[inline] def relLakeDir (_ : Package) : FilePath :=
  defaultLakeDir

/-- The full path to the package's Lake directory (i.e, `dir` joined with `relLakeDir`). -/
@[inline] def lakeDir (self : Package) : FilePath :=
  self.dir / self.relLakeDir

/-- The path for storing the package's remote dependencies relative to `dir` (i.e., `packagesDir`). -/
@[inline] def relPkgsDir (self : Package) : FilePath :=
  self.config.packagesDir.normalize

/-- The package's `dir` joined with its `relPkgsDir`. -/
@[inline] def pkgsDir (self : Package) : FilePath :=
  self.dir / self.relPkgsDir

/-- The path to the package's JSON manifest of remote dependencies. -/
@[inline] def manifestFile (self : Package) : FilePath :=
  self.dir / self.relManifestFile

/-- The package's `dir` joined with its `buildDir` configuration. -/
@[inline] def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir.normalize

/-- The package's `testDriverArgs` configuration. -/
@[inline] def testDriverArgs (self : Package) : Array String :=
  self.config.testDriverArgs

/-- The package's `lintDriverArgs` configuration. -/
@[inline] def lintDriverArgs (self : Package) : Array String :=
  self.config.lintDriverArgs

/-- The package's `extraDepTargets` configuration. -/
@[inline] def extraDepTargets (self : Package) : Array Name :=
  self.config.extraDepTargets

/-- The package's `platformIndependent` configuration. -/
@[inline] def platformIndependent (self : Package) : Option Bool :=
  self.config.platformIndependent

/-- The package's `releaseRepo`/`releaseRepo?` configuration. -/
@[inline] def releaseRepo? (self : Package) : Option String :=
  self.config.releaseRepo

/-- The packages `remoteUrl` as an `Option` (`none` if empty). -/
@[inline] def remoteUrl? (self : Package) : Option String :=
  if self.remoteUrl.isEmpty then some self.remoteUrl else none

/-- The package's `lakeDir` joined with its `buildArchive`. -/
@[inline] def buildArchiveFile (self : Package) : FilePath :=
  self.lakeDir / self.buildArchive

/-- The path where Lake stores the package's barrel (downloaded from Reservoir). -/
@[inline] def barrelFile (self : Package) : FilePath :=
  self.lakeDir / "build.barrel"

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

/-- The package's `dynlibs` configuration. -/
@[inline] def dynlibs (self : Package) : TargetArray Dynlib :=
  self.config.dynlibs

/-- The package's `plugins` configuration. -/
@[inline] def plugins (self : Package) : TargetArray Dynlib :=
  self.config.plugins

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

/-- The package's `moreLinkObjs` configuration. -/
@[inline] def moreLinkObjs (self : Package) : TargetArray FilePath :=
  self.config.moreLinkObjs

/-- The package's `moreLinkLibs` configuration. -/
@[inline] def moreLinkLibs (self : Package) : TargetArray Dynlib :=
  self.config.moreLinkLibs

/-- The package's `moreLinkArgs` configuration. -/
@[inline] def moreLinkArgs (self : Package) : Array String :=
  self.config.moreLinkArgs

/-- The package's `weakLinkArgs` configuration. -/
@[inline] def weakLinkArgs (self : Package) : Array String :=
  self.config.weakLinkArgs

/-- The package's `dir` joined with its `srcDir` configuration. -/
@[inline] def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir.normalize

/-- The package's root directory for `lean` (i.e., `srcDir`). -/
@[inline] def rootDir (self : Package) : FilePath :=
  self.srcDir

/-- The package's `buildDir` joined with its `leanLibDir` configuration. -/
@[inline] def leanLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.leanLibDir.normalize

/--
Where static libraries for the package are located.
The package's `buildDir` joined with its `nativeLibDir` configuration.
-/
@[inline] def staticLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.nativeLibDir.normalize

/--
Where shared libraries for the package are located.
The package's `buildDir` joined with its `nativeLibDir` configuration.
-/
@[inline] def sharedLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.nativeLibDir.normalize

/-- The package's `buildDir` joined with its `nativeLibDir` configuration. -/
@[inline, deprecated "Use staticLibDir or sharedLibDir instead." (since := "2025-03-29")]
def nativeLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.nativeLibDir.normalize

/-- The package's `buildDir` joined with its `binDir` configuration. -/
@[inline] def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir.normalize

/-- The package's `buildDir` joined with its `irDir` configuration. -/
@[inline] def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir.normalize

/-- Try to find a target configuration in the package with the given name. -/
def findTargetDecl? (name : Name) (self : Package) : Option (NConfigDecl self.name name) :=
  self.targetDeclMap.find? name

/-- Whether the given module is considered local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.targetDecls.any (·.leanLibConfig?.any (·.isLocalModule mod))

/-- Whether the given module is in the package (i.e., can build it). -/
def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.targetDecls.any fun t =>
    t.leanLibConfig?.any (·.isBuildableModule mod) ||
    t.leanExeConfig?.any (·.root == mod)

/-- Remove the package's build outputs (i.e., delete its build directory). -/
def clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir
