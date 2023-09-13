/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package

namespace Lake
open Lean System

/-- A Lean library -- its package plus its configuration. -/
structure LeanLib where
  /-- The package the library belongs to. -/
  pkg : Package
   /-- The library's user-defined configuration. -/
  config : LeanLibConfig

/-- The Lean libraries of the package (as an Array). -/
@[inline] def Package.leanLibs (self : Package) : Array LeanLib :=
  self.leanLibConfigs.foldl (fun a v => a.push ⟨self, v⟩) #[]

/-- Try to find a Lean library in the package with the given name. -/
@[inline] def Package.findLeanLib? (name : Name) (self : Package) : Option LeanLib :=
  self.leanLibConfigs.find? name |>.map (⟨self, ·⟩)

namespace LeanLib

/-- The library's well-formed name. -/
@[inline] def name (self : LeanLib) : Name :=
  self.config.name

/-- The package's `srcDir` joined with the library's `srcDir`. -/
@[inline] def srcDir (self : LeanLib) : FilePath :=
  self.pkg.srcDir / self.config.srcDir

/-- The library's root directory for `lean` (i.e., `srcDir`). -/
@[inline] def rootDir (self : LeanLib) : FilePath :=
  self.srcDir

/--
The names of the library's root modules
(i.e., the library's `roots` configuration).
-/
@[inline] def roots (self : LeanLib) : Array Name :=
  self.config.roots

/-- Whether the given module is considered local to the library. -/
@[inline] def isLocalModule (mod : Name) (self : LeanLib) : Bool :=
  self.config.isLocalModule mod

/-- Whether the given module is a buildable part of the library. -/
@[inline] def isBuildableModule (mod : Name) (self : LeanLib) : Bool :=
  self.config.isBuildableModule mod

/-- The file name of the library's static binary (i.e., its `.a`) -/
@[inline] def staticLibFileName (self : LeanLib) : FilePath :=
  nameToStaticLib self.config.libName

/-- The path to the static library in the package's `libDir`. -/
@[inline] def staticLibFile (self : LeanLib) : FilePath :=
  self.pkg.nativeLibDir / self.staticLibFileName

/-- The file name of the library's shared binary (i.e., its `dll`, `dylib`, or `so`) . -/
@[inline] def sharedLibFileName (self : LeanLib) : FilePath :=
  nameToSharedLib self.config.libName

/-- The path to the shared library in the package's `libDir`. -/
@[inline] def sharedLibFile (self : LeanLib) : FilePath :=
  self.pkg.nativeLibDir / self.sharedLibFileName

/-- The library's `extraDepTargets` configuration. -/
@[inline] def extraDepTargets (self : LeanLib) :=
  self.config.extraDepTargets

/--
Whether to precompile the library's modules.
Is true if either the package or the library have `precompileModules` set.
-/
@[inline] def precompileModules (self : LeanLib) : Bool :=
  self.pkg.precompileModules || self.config.precompileModules

/-- The library's `defaultFacets` configuration. -/
@[inline] def defaultFacets (self : LeanLib) : Array Name :=
  self.config.defaultFacets

/-- The library's `nativeFacets` configuration. -/
@[inline] def nativeFacets (self : LeanLib) : Array (ModuleFacet (BuildJob FilePath)) :=
  self.config.nativeFacets

/--
The build type for modules of this library.
That is, the minimum of package's `buildType` and the library's  `buildType`.
-/
@[inline] def buildType (self : LeanLib) : BuildType :=
  min self.pkg.buildType self.config.buildType

/--
The backend type for modules of this library.
Prefer the library's `backend` configuration, then the package's,
then the default (which is C for now).
-/
@[inline] def backend (self : LeanLib) : Backend :=
  Backend.orPreferLeft self.config.backend self.pkg.backend
/--
The arguments to pass to `lean` when compiling the library's Lean files.
That is, the package's `moreLeanArgs` plus the library's  `moreLeanArgs`.
-/
@[inline] def leanArgs (self : LeanLib) : Array String :=
  self.pkg.moreLeanArgs ++ self.config.moreLeanArgs

/--
The arguments to weakly pass to `lean` when compiling the library's Lean files.
That is, the package's `weakLeanArgs` plus the library's  `weakLeanArgs`.
-/
@[inline] def weakLeanArgs (self : LeanLib) : Array String :=
  self.pkg.weakLeanArgs ++ self.config.weakLeanArgs

/--
The arguments to pass to `leanc` when compiling the library's Lean-produced C files.
That is, the build type's `leancArgs`, the package's `moreLeancArgs`,
and then the library's `moreLeancArgs`.
-/
@[inline] def leancArgs (self : LeanLib) : Array String :=
  self.buildType.leancArgs ++ self.pkg.moreLeancArgs ++ self.config.moreLeancArgs

/--
The arguments to weakly pass to `leanc` when compiling the library's Lean-produced C files.
That is, the package's `weakLeancArgs` plus the library's  `weakLeancArgs`.
-/
@[inline] def weakLeancArgs (self : LeanLib) : Array String :=
  self.pkg.weakLeancArgs ++ self.config.weakLeancArgs

/--
The arguments to pass to `leanc` when linking the shared library.
That is, the package's `moreLinkArgs` plus the library's  `moreLinkArgs`.
-/
@[inline] def linkArgs (self : LeanLib) : Array String :=
  self.pkg.moreLinkArgs ++ self.config.moreLinkArgs

/--
The arguments to weakly pass to `leanc` when linking the shared library.
That is, the package's `weakLinkArgs` plus the library's  `weakLinkArgs`.
-/
@[inline] def weakLinkArgs (self : LeanLib) : Array String :=
  self.pkg.weakLinkArgs ++ self.config.weakLinkArgs
