/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.ConfigTarget
public import Lake.Util.NativeLib
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

namespace Lake
open Lean System

/-- A Lean library -- its package plus its configuration. -/
public abbrev LeanLib := ConfigTarget LeanLib.configKind

/-- The Lean libraries of the package (as an Array). -/
@[inline] public def Package.leanLibs (self : Package) : Array LeanLib :=
  self.configTargets LeanLib.configKind

/-- Try to find a Lean library in the package with the given name. -/
@[inline] public def Package.findLeanLib? (name : Name) (self : Package) : Option LeanLib :=
  self.findConfigTarget? LeanLib.configKind name

namespace LeanLib

/-- The library's user-defined configuration. -/
@[inline] public nonrec def config (self : LeanLib) : LeanLibConfig self.name :=
  self.config

/-- The package's `srcDir` joined with the library's `srcDir`. -/
@[inline] public def srcDir (self : LeanLib) : FilePath :=
  self.pkg.srcDir / self.config.srcDir.normalize

/-- The library's root directory for `lean` (i.e., `srcDir`). -/
@[inline] public def rootDir (self : LeanLib) : FilePath :=
  self.srcDir

/--
The names of the library's root modules
(i.e., the library's `roots` configuration).
-/
@[inline] public def roots (self : LeanLib) : Array Name :=
  self.config.roots

/-- Whether the given module is considered local to the library. -/
@[inline] public def isLocalModule (mod : Name) (self : LeanLib) : Bool :=
  self.config.isLocalModule mod

/-- Whether the given module is a buildable part of the library. -/
@[inline] public def isBuildableModule (mod : Name) (self : LeanLib) : Bool :=
  self.config.isBuildableModule mod

/-- Whether this library's native binaries should be prefixed with `lib` on Windows. -/
@[inline] public def libPrefixOnWindows (self : LeanLib) : Bool :=
  self.config.libPrefixOnWindows || self.pkg.libPrefixOnWindows

/-- The name of the native library (e.g., what is passed to `-l`). -/
public def libName (self : LeanLib) : String :=
  let libName :=
    if self.config.libName.isEmpty then
      mkModuleInitializationStem self.name self.pkg.id?
    else self.config.libName
  if self.libPrefixOnWindows && System.Platform.isWindows then
    s!"lib{libName}"
  else libName

/-- The file name of the library's static binary (i.e., its `.a`) -/
@[inline] public def staticLibFileName (self : LeanLib) : FilePath :=
  nameToStaticLib self.libName

/-- The path to the static library in the package's `libDir`. -/
@[inline] public def staticLibFile (self : LeanLib) : FilePath :=
  self.pkg.staticLibDir / self.staticLibFileName

/-- The path to the static library (with exported symbols) in the package's `libDir`. -/
@[inline] public def staticExportLibFile (self : LeanLib) : FilePath :=
  self.pkg.staticLibDir / self.staticLibFileName.addExtension "export"

/-- The file name of the library's shared binary (i.e., its `dll`, `dylib`, or `so`) . -/
@[inline] public def sharedLibFileName (self : LeanLib) : FilePath :=
  nameToSharedLib self.libName

/-- The path to the shared library in the package's `libDir`. -/
@[inline] public def sharedLibFile (self : LeanLib) : FilePath :=
  self.pkg.sharedLibDir / self.sharedLibFileName

/-- Whether the shared binary of this library is a valid plugin. -/
public def isPlugin (self : LeanLib) : Bool :=
  if h : self.roots.size = 1 then
    self.libName == mkModuleInitializationStem self.roots[0] self.pkg.id?
  else false

/-- The library's `extraDepTargets` configuration. -/
@[inline] public def extraDepTargets (self : LeanLib) :=
  self.config.extraDepTargets

/--
Whether to precompile the library's modules.
Is true if either the package or the library have `precompileModules` set.
-/
@[inline] public def precompileModules (self : LeanLib) : Bool :=
  self.pkg.precompileModules || self.config.precompileModules

/--
Whether to the library's Lean code is platform-independent.
Returns the library's `platformIndependent` configuration if non-`none`.
Otherwise, falls back to the package's.
-/
@[inline] public def platformIndependent (self : LeanLib) : Option Bool :=
  self.config.platformIndependent <|> self.pkg.platformIndependent

/-- The library's `defaultFacets` configuration. -/
@[inline] public def defaultFacets (self : LeanLib) : Array Name :=
  self.config.defaultFacets

/-- The library's `nativeFacets` configuration. -/
@[inline] public def nativeFacets (self : LeanLib) (shouldExport : Bool) : Array (ModuleFacet FilePath) :=
  self.config.nativeFacets shouldExport

/--
The build type for modules of this library.
That is, the minimum of package's `buildType` and the library's  `buildType`.
-/
@[inline] public def buildType (self : LeanLib) : BuildType :=
  min self.pkg.buildType self.config.buildType

/--
The arguments to pass to `lean --server` when running the Lean language server.
`serverOptions` is the accumulation of:
- the build type's `leanOptions`
- the package's `leanOptions`
- the package's `moreServerOptions`
- the library's `leanOptions`
- the library's `moreServerOptions`
-/
@[inline] public def serverOptions (self : LeanLib) : LeanOptions :=
  ({} : LeanOptions) ++ self.buildType.leanOptions ++ self.pkg.moreServerOptions ++
  self.config.leanOptions ++ self.config.moreServerOptions

/--
The backend type for modules of this library.
Prefer the library's `backend` configuration, then the package's,
then the default (which is C for now).
-/
@[inline] public def backend (self : LeanLib) : Backend :=
  Backend.orPreferLeft self.config.backend self.pkg.backend

/--
Whether downstream packages can `import all` modules of this library.
Enabled if either the library or the package enables it.
-/
@[inline] public def allowImportAll (self : LeanLib) : Bool :=
  self.config.allowImportAll || self.pkg.allowImportAll

/--
The dynamic libraries to load for modules of this library.
The targets of the package plus the targets of the library (in that order).
-/
@[inline] public def dynlibs (self : LeanLib) : TargetArray Dynlib :=
  self.pkg.dynlibs ++ self.config.dynlibs

/--
The Lean plugins for modules of this library.
The targets of the package plus the targets of the library (in that order).
-/
@[inline] public def plugins (self : LeanLib) : TargetArray Dynlib :=
  self.pkg.plugins ++ self.config.plugins

/--
The arguments to pass to `lean` when compiling the library's Lean files.
`leanArgs` is the accumulation of:
- the build type's `leanOptions`
- the package's `leanOptions`
- the library's `leanOptions`
-/
@[inline] public def leanOptions (self : LeanLib) : LeanOptions :=
  self.buildType.leanOptions ++ self.pkg.leanOptions ++ self.config.leanOptions

/--
The arguments to pass to `lean` when compiling the library's Lean files.
`leanArgs` is the accumulation of:
- the build type's `leanArgs`
- the package's `moreLeanArgs`
- the library's `moreLeanArgs`
-/
@[inline] public def leanArgs (self : LeanLib) : Array String :=
 self.buildType.leanArgs ++ self.pkg.moreLeanArgs ++ self.config.moreLeanArgs

/--
The arguments to weakly pass to `lean` when compiling the library's Lean files.
That is, the package's `weakLeanArgs` plus the library's  `weakLeanArgs`.
-/
@[inline] public def weakLeanArgs (self : LeanLib) : Array String :=
  self.pkg.weakLeanArgs ++ self.config.weakLeanArgs

/--
The arguments to pass to `leanc` when compiling the library's Lean-produced C files.
That is, the build type's `leancArgs`, the package's `moreLeancArgs`,
and then the library's `moreLeancArgs`.
-/
@[inline] public def leancArgs (self : LeanLib) : Array String :=
  self.buildType.leancArgs ++ self.pkg.moreLeancArgs ++ self.config.moreLeancArgs

/--
The arguments to weakly pass to `leanc` when compiling the library's Lean-produced C files.
That is, the package's `weakLeancArgs` plus the library's `weakLeancArgs`.
-/
@[inline] public def weakLeancArgs (self : LeanLib) : Array String :=
  self.pkg.weakLeancArgs ++ self.config.weakLeancArgs

/--
Additionl target objects to pass to `ar` when linking the static library.
That is, the package's `moreLinkObjs` plus the library's `moreLinkObjs`.
-/
@[inline] public def moreLinkObjs (self : LeanLib) : TargetArray FilePath :=
  self.pkg.moreLinkObjs ++ self.config.moreLinkObjs

/-
Additionl target libraries to are linked to the shared library.
That is, the package's `moreLinkLibs` plus the library's `moreLinkLibs`.
-/
@[inline] public def moreLinkLibs (self : LeanLib) : TargetArray Dynlib :=
  self.pkg.moreLinkLibs ++ self.config.moreLinkLibs

/--
The arguments to pass to `leanc` when linking the shared library.
That is, the package's `moreLinkArgs` plus the library's `moreLinkArgs`.
-/
@[inline] public def linkArgs (self : LeanLib) : Array String :=
  self.pkg.moreLinkArgs ++ self.config.moreLinkArgs

/--
The arguments to weakly pass to `leanc` when linking the shared library.
That is, the package's `weakLinkArgs` plus the library's `weakLinkArgs`.
-/
@[inline] public def weakLinkArgs (self : LeanLib) : Array String :=
  self.pkg.weakLinkArgs ++ self.config.weakLinkArgs
