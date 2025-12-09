/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Lake.Config.Cache
public import Lake.Config.Script
public import Lake.Config.ConfigDecl
public import Lake.Config.Dependency
public import Lake.Config.PackageConfig
public import Lake.Util.FilePath -- use scoped instance downstream
public import Lake.Util.OrdHashSet
public import Lake.Util.Name
meta import all Lake.Util.OpaqueType

open System Lean

namespace Lake

public nonempty_type OpaquePostUpdateHook (pkg : Name)

/-- A Lake package -- its location plus its configuration. -/
public structure Package where
  /-- The index of the package in the workspace. Used to disambiguate packages with the same name. -/
  wsIdx : Nat
  /-- The assigned name of the package. -/
  baseName : Name
  /-- The package identifier used in target keys and configuration types. -/
  keyName : Name := baseName.num wsIdx
  /-- The name specified by the package. -/
  origName : Name
  /-- The absolute path to the package's directory. -/
  dir : FilePath
  /-- The path to the package's directory relative to the workspace. -/
  relDir : FilePath
  /-- The package's user-defined configuration. -/
  config : PackageConfig keyName origName
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
  targetDecls : Array (PConfigDecl keyName) := #[]
  /-- Name-declaration map of target configurations in the package. -/
  targetDeclMap : DNameMap (NConfigDecl keyName) :=
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
  postUpdateHooks : Array (OpaquePostUpdateHook keyName) := #[]
  /-- The package's `buildArchive`/`buildArchive?` configuration. -/
  buildArchive : String :=
    if let some n := config.buildArchive then n else defaultBuildArchive baseName
  /-- The driver used for `lake test` when this package is the workspace root. -/
  testDriver : String := config.testDriver
  /-- The driver used for `lake lint` when this package is the workspace root. -/
  lintDriver : String := config.lintDriver
  /--
  Input-to-output(s) map for hashes of package artifacts.
  If `none`, the artifact cache is disabled for the package.
  -/
  inputsRef? : Option CacheRef := none
  /--
  Input-to-output(s) map for hashes of package artifacts.
  If `none`, the artifact cache is disabled for the package.
  -/
  outputsRef? : Option CacheRef := none

deriving Inhabited

namespace Package

public instance : Hashable Package where hash pkg := hash pkg.keyName
public instance : BEq Package where beq p1 p2 := p1.wsIdx == p2.wsIdx

/-- Pretty prints the package's name. Used when outputting package names. -/
@[inline] public def prettyName (self : Package) : String :=
  self.baseName.toString (escape := false)

public instance : QueryJson Package := ⟨(toJson ·.keyName)⟩
public instance : QueryText Package := ⟨(·.prettyName)⟩

@[deprecated "Use `baseName`, `keyName`, or `prettyName` instead" (since := "2025-12-03")]
public abbrev name := @baseName

/-- The (unscoped) name of the package as it appears in Reservoir URLs (before URI-encoding). -/
@[inline] public def reservoirName (self : Package) : String :=
  self.origName.toString (escape := false)

end Package

public abbrev PackageSet := Std.HashSet Package
@[inline] public def PackageSet.empty : PackageSet := ∅

public abbrev OrdPackageSet := OrdHashSet Package
@[inline] public def OrdPackageSet.empty : OrdPackageSet := OrdHashSet.empty

/-- A package with a name known at type-level. -/
public structure NPackage (n : Name) extends Package where
  keyName_eq : toPackage.keyName = n

namespace NPackage

set_option linter.deprecated false in
@[deprecated keyName_eq (since := "2025-12-03")]
public theorem name_eq {self : NPackage n} : self.toPackage.keyName = n := self.keyName_eq

attribute [simp] NPackage.keyName_eq

public instance : CoeOut (NPackage n) Package := ⟨NPackage.toPackage⟩
public instance : CoeDep Package pkg (NPackage pkg.keyName) := ⟨⟨pkg, rfl⟩⟩

end NPackage

/--
The type of a post-update hooks monad.
`IO` equipped with logging ability and information about the Lake configuration.
-/
public abbrev PostUpdateFn (pkgName : Name) := NPackage pkgName → LakeT LogIO PUnit

public structure PostUpdateHook (pkgName : Name) where
  fn : PostUpdateFn pkgName
  deriving Inhabited

public hydrate_opaque_type OpaquePostUpdateHook PostUpdateHook name

public structure PostUpdateHookDecl where
  pkg : Name
  fn : PostUpdateFn pkg
  deriving TypeName

namespace Package

/-- Returns whether this package is root package of the workspace. -/
@[inline] public def isRoot (self : Package) : Bool  :=
  self.wsIdx == 0

/-- **For internal use.** Whether this package is Lean itself.  -/
@[inline] public def bootstrap (self : Package) : Bool  :=
  self.config.bootstrap

/-- The identifier passed to Lean to disambiguate the package's native symbols. -/
public def id? (self : Package) : Option PkgId :=
  if self.bootstrap then none else some <| self.origName.toString (escape := false)

/-- The package version. -/
@[inline] public def version (self : Package) : LeanVer  :=
  self.config.version

/-- The package's `versionTags` configuration. -/
@[inline] public def versionTags (self : Package) : StrPat  :=
  self.config.versionTags

/-- The package's `description` configuration. -/
@[inline] public def description (self : Package) : String  :=
  self.config.description

/-- The package's `keywords` configuration. -/
@[inline] public def keywords (self : Package) : Array String  :=
  self.config.keywords

/-- The package's `homepage` configuration. -/
@[inline] public def homepage (self : Package) : String  :=
  self.config.homepage

/-- The package's `reservoir` configuration. -/
@[inline] public def reservoir (self : Package) : Bool  :=
  self.config.reservoir

/-- The package's `license` configuration. -/
@[inline] public def license (self : Package) : String  :=
  self.config.license

/-- The package's `licenseFiles` configuration. -/
@[inline] public def relLicenseFiles (self : Package) : Array FilePath :=
  self.config.licenseFiles.map (·.normalize)

/-- The package's `dir` joined with each of its `relLicenseFiles`. -/
@[inline] public def licenseFiles (self : Package) : Array FilePath  :=
  self.relLicenseFiles.map (self.dir / ·.normalize)

/-- The package's `readmeFile` configuration. -/
@[inline] public def relReadmeFile (self : Package) : FilePath  :=
  self.config.readmeFile.normalize

/-- The package's `dir` joined with its `relReadmeFile`. -/
@[inline] public def readmeFile (self : Package) : FilePath  :=
  self.dir / self.relReadmeFile

/-- The path to the package's Lake directory relative to `dir` (e.g., `.lake`). -/
@[inline] public def relLakeDir (_ : Package) : FilePath :=
  defaultLakeDir

/-- The full path to the package's Lake directory (i.e, `dir` joined with `relLakeDir`). -/
@[inline] public def lakeDir (self : Package) : FilePath :=
  self.dir / self.relLakeDir

/-- The path for storing the package's remote dependencies relative to `dir` (i.e., `packagesDir`). -/
@[inline] public def relPkgsDir (self : Package) : FilePath :=
  self.config.packagesDir.normalize

/-- The package's `dir` joined with its `relPkgsDir`. -/
@[inline] public def pkgsDir (self : Package) : FilePath :=
  self.dir / self.relPkgsDir

/-- The path to the package's JSON manifest of remote dependencies. -/
@[inline] public def manifestFile (self : Package) : FilePath :=
  self.dir / self.relManifestFile

/-- The package's `dir` joined with its `buildDir` configuration. -/
@[inline] public def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir.normalize

/-- The package's `testDriverArgs` configuration. -/
@[inline] public def testDriverArgs (self : Package) : Array String :=
  self.config.testDriverArgs

/-- The package's `lintDriverArgs` configuration. -/
@[inline] public def lintDriverArgs (self : Package) : Array String :=
  self.config.lintDriverArgs

/-- The package's `extraDepTargets` configuration. -/
@[inline] public def extraDepTargets (self : Package) : Array Name :=
  self.config.extraDepTargets

/-- The package's `platformIndependent` configuration. -/
@[inline] public def platformIndependent (self : Package) : Option Bool :=
  self.config.platformIndependent

/-- Whether the package's  has been configured with `platformIndependent = true`. -/
@[inline] public def isPlatformIndependent (self : Package) : Bool :=
  self.config.platformIndependent == some true

/-- The package's `releaseRepo`/`releaseRepo?` configuration. -/
@[inline] public def releaseRepo? (self : Package) : Option String :=
  self.config.releaseRepo

/-- The packages `remoteUrl` as an `Option` (`none` if empty). -/
@[inline] public def remoteUrl? (self : Package) : Option String :=
  if self.remoteUrl.isEmpty then some self.remoteUrl else none

/-- The package's `lakeDir` joined with its `buildArchive`. -/
@[inline] public def buildArchiveFile (self : Package) : FilePath :=
  self.lakeDir / self.buildArchive

/-- The path where Lake stores the package's barrel (downloaded from Reservoir). -/
@[inline] public def barrelFile (self : Package) : FilePath :=
  self.lakeDir / "build.barrel"

/-- The package's `preferReleaseBuild` configuration. -/
@[inline] public def preferReleaseBuild (self : Package) : Bool :=
  self.config.preferReleaseBuild

/-- The package's `precompileModules` configuration. -/
@[inline] public def precompileModules (self : Package) : Bool :=
  self.config.precompileModules

/-- The package's `moreGlobalServerArgs` configuration. -/
@[inline] public def moreGlobalServerArgs (self : Package) : Array String :=
  self.config.moreGlobalServerArgs

/-- The package's `moreServerOptions` configuration appended to its `leanOptions` configuration. -/
@[inline] public def moreServerOptions (self : Package) : LeanOptions :=
  LeanOptions.ofArray self.config.leanOptions ++ self.config.moreServerOptions

/-- The package's `buildType` configuration. -/
@[inline] public def buildType (self : Package) : BuildType :=
  self.config.buildType

/-- The package's `backend` configuration. -/
@[inline] public def backend (self : Package) : Backend :=
  self.config.backend

/-- The package's `allowImportAll` configuration. -/
@[inline] public def allowImportAll (self : Package) : Bool :=
  self.config.allowImportAll

/-- The package's `dynlibs` configuration. -/
@[inline] public def dynlibs (self : Package) : TargetArray Dynlib :=
  self.config.dynlibs

/-- The package's `plugins` configuration. -/
@[inline] public def plugins (self : Package) : TargetArray Dynlib :=
  self.config.plugins

/-- The package's `leanOptions` configuration. -/
@[inline] public def leanOptions (self : Package) : LeanOptions :=
  .ofArray self.config.leanOptions

/-- The package's `moreLeanArgs` configuration. -/
@[inline] public def moreLeanArgs (self : Package) : Array String :=
  self.config.moreLeanArgs

/-- The package's `weakLeanArgs` configuration. -/
@[inline] public def weakLeanArgs (self : Package) : Array String :=
  self.config.weakLeanArgs

/-- The package's `moreLeancArgs` configuration. -/
@[inline] public def moreLeancArgs (self : Package) : Array String :=
  self.config.moreLeancArgs

/-- The package's `weakLeancArgs` configuration. -/
@[inline] public def weakLeancArgs (self : Package) : Array String :=
  self.config.weakLeancArgs

/-- The package's `moreLinkObjs` configuration. -/
@[inline] public def moreLinkObjs (self : Package) : TargetArray FilePath :=
  self.config.moreLinkObjs

/-- The package's `moreLinkLibs` configuration. -/
@[inline] public def moreLinkLibs (self : Package) : TargetArray Dynlib :=
  self.config.moreLinkLibs

/-- The package's `moreLinkArgs` configuration. -/
@[inline] public def moreLinkArgs (self : Package) : Array String :=
  self.config.moreLinkArgs

/-- The package's `weakLinkArgs` configuration. -/
@[inline] public def weakLinkArgs (self : Package) : Array String :=
  self.config.weakLinkArgs

/-- The package's `dir` joined with its `srcDir` configuration. -/
@[inline] public def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir.normalize

/-- The package's root directory for `lean` (i.e., `srcDir`). -/
@[inline] public def rootDir (self : Package) : FilePath :=
  self.srcDir

/-- The package's `buildDir` joined with its `leanLibDir` configuration. -/
@[inline] public def leanLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.leanLibDir.normalize

/--
Where static libraries for the package are located.
The package's `buildDir` joined with its `nativeLibDir` configuration.
-/
@[inline] public def staticLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.nativeLibDir.normalize

/--
Where shared libraries for the package are located.
The package's `buildDir` joined with its `nativeLibDir` configuration.
-/
@[inline] public def sharedLibDir (self : Package) : FilePath :=
  self.buildDir / self.config.nativeLibDir.normalize

/-- The package's `buildDir` joined with its `binDir` configuration. -/
@[inline] public def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir.normalize

/-- The package's `buildDir` joined with its `irDir` configuration. -/
@[inline] public def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir.normalize

/-- The package's `libPrefixOnWindows` configuration. -/
@[inline] public def libPrefixOnWindows (self : Package) : Bool :=
  self.config.libPrefixOnWindows

/-- The package's `enableArtifactCache?` configuration. -/
@[inline] public def enableArtifactCache? (self : Package) : Option Bool :=
  self.config.enableArtifactCache?

/-- The package's `restoreAllArtifacts` configuration. -/
@[inline] public def restoreAllArtifacts (self : Package) : Bool :=
  self.config.restoreAllArtifacts

/-- The directory within the Lake cache were package-scoped files are stored. -/
public def cacheScope (self : Package) :=
  self.baseName.toString (escape := false)

/-- Try to find a target configuration in the package with the given name. -/
public def findTargetDecl? (name : Name) (self : Package) : Option (NConfigDecl self.keyName name) :=
  self.targetDeclMap.get? name

/-- Whether the given module is considered local to the package. -/
public def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.targetDecls.any (·.leanLibConfig?.any (·.isLocalModule mod))

/-- Whether the given module is in the package (i.e., can build it). -/
public def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.targetDecls.any fun t =>
    t.leanLibConfig?.any (·.isBuildableModule mod) ||
    t.leanExeConfig?.any (·.root == mod)

/-- Remove the package's build outputs (i.e., delete its build directory). -/
public def clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir
