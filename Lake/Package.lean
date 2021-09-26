/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Std.Data.HashMap
import Lake.LeanVersion
import Lake.BuildTarget
import Lake.Glob

open Std System
open Lean (Name)

namespace Lake

--------------------------------------------------------------------------------
-- # Defaults
--------------------------------------------------------------------------------

/-- The default setting for a `PackageConfig`'s `buildDir` option. -/
def defaultBuildDir : FilePath := "build"

/-- The default setting for a `PackageConfig`'s `binDir` option. -/
def defaultBinDir : FilePath := "bin"

/-- The default setting for a `PackageConfig`'s `libDir` option. -/
def defaultLibDir : FilePath := "lib"

/-- The default setting for a `PackageConfig`'s `oleanDir` option. -/
def defaultOleanDir : FilePath := "lib"

/-- The default setting for a `PackageConfig`'s `irDir` option. -/
def defaultIrDir : FilePath := "ir"

/-- The default setting for a `PackageConfig`'s `depsDir` option. -/
def defaultDepsDir : FilePath := "lean_packages"

--------------------------------------------------------------------------------
-- # PackageConfig Helpers
--------------------------------------------------------------------------------

/--
  The `src` of a `Dependency`.

  In Lake, dependency sources currently come into flavors:
  * Local `path`s relative to the package's directory.
  * Remote `git` repositories that are download from a given `url`
    into the packages's `depsDir`.
-/
inductive Source where
| path (dir : FilePath) : Source
| git (url rev : String) (branch : Option String) : Source
deriving Inhabited, Repr

/-- A `Dependency` of a package. -/
structure Dependency where
  /--
    A name for the dependency.
    The names of a package's dependencies cannot clash.
  -/
  name : String
  /--
    The source of a dependency.
    See the documentation of `Source` for more information.
  -/
  src  : Source
  /--
    The subdirectory of the dependency's source where
    the dependency's package configuration is located.
  -/
  dir  : FilePath := "."
  /--
    Arguments to pass to the dependency's package configuration.
  -/
  args : List String := []

deriving Inhabited, Repr

/--
  A package `Script` is an arbitrary function that is
  indexed by a `String` key and can be be run by `lake run <key> [-- <args>]`.
-/
abbrev Script := (args : List String) → IO PUnit

--------------------------------------------------------------------------------
-- # PackageConfig
--------------------------------------------------------------------------------

/-- A package's declarative configuration. -/
structure PackageConfig where

  /--
    The name of the package.
  -/
  name : String

  /--
    A `HashMap` of scripts for the package.

    A `Script` is an arbitrary `(args : List String) → IO PUnit` function that
    is indexed by a `String` key and can be be run by `lake run <key> [-- <args>]`.
  -/
  scripts : HashMap String Script := HashMap.empty

  /-
    A `List` of the package's dependencies.
    See the documentation of `Dependency` for more information.
  -/
  dependencies : List Dependency := []

  /--
    The directory to which Lake should download dependencies.
    Defaults to `defaultDepsDir` (i.e., `lean_packages`).
  -/
  depsDir : FilePath := defaultDepsDir

  /--
    An extra `OpaqueTarget` that should be built before the package.

    `OpaqueTarget.collectList/collectArray` can be used combine multiple
    targets into a single `extraDepTarget`.
  -/
  extraDepTarget : OpaqueTarget := Target.nil

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

  /-
    The root module(s) of the package's library.

    Submodules of these roots (e.g., `Pkg.Foo` of `Pkg`) are considered
    part of the package.

    Defaults to a single root of the package's uppercase `name`.
  -/
  libRoots : Array Name := #[name.capitalize]

  /--
    An `Array` of module `Glob`s to build for the package's library.
    Defaults to a `Glob.one` of each of the module's `libRoots`.

    Submodule globs build every source file within their directory.
    Local imports of glob'ed files (i.e., fellow modules of the package) are
    also recursively built.
  -/
  libGlobs : Array Glob := libRoots.map Glob.one

  /--
    Additional arguments to pass to `lean` while compiling Lean source files.
  -/
  leanArgs : Array String := #[]

  /--
    Additional arguments to pass to `leanc`
    while compiling the C source files generated by `lean`.
    Defaults to `-03` and `-DNDEBUG`.
  -/
  leancArgs : Array String := #["-O3", "-DNDEBUG"]

  /--
    The build subdirectory to which Lake should output
    the package's intermediary results (e.g., `.c` and `.o` files).
    Defaults to `defaultIrDir` (i.e., `ir`).
  -/
  irDir : FilePath := defaultIrDir

  /--
    The name of the package's static library.
    Defaults to the package's uppercase `name`.
  -/
  libName : String := name.capitalize

  /--
    The build subdirectory to which Lake should output the package's static library.
    Defaults to `defaultLibDir` (i.e., `lib`).
  -/
  libDir : FilePath := defaultLibDir

  /--
    The name of the package's binary executable.
    Defaults to the package's `name`.
  -/
  binName : String := name

  /--
    The name of the package's binary executable.
    Defaults to the package's `name`.
  -/
  binDir : FilePath := defaultBinDir

  /--
    The root module of the package's binary executable.
    Defaults to the package's uppercase `name`.

    The root is built by recursively building its
    local imports (i.e., fellow modules of the package).

    This setting is most useful for packages that are distributing both a
    library and a binary (like Lake itself). In such cases, it is common for
    there to be code (e.g., `main`) that is needed for the binary but should
    not be included in the library proper.
  -/
  binRoot : Name := name.capitalize

  /--
    Additional library `FileTarget`s
      (beyond the package's and its dependencies' libraries)
    to build and link to the package's binary executable
      (and/or to dependent package's executables).
  -/
  moreLibTargets : Array FileTarget := #[]

  /--
    Additional arguments to pass to `leanc`
      while compiling the package's binary executable.
    These will come *after* the paths of libraries built with `moreLibTargets`.
  -/
  linkArgs : Array String := #[]

deriving Inhabited

--------------------------------------------------------------------------------
-- # Package
--------------------------------------------------------------------------------

/-- A Lake package -- its location plus its configuration. -/
structure Package where
  /-- The path to the package's directory. -/
  dir : FilePath
  /-- The package's configuration. -/
  config : PackageConfig
  deriving Inhabited

/--
  An alternate signature for package configurations
  that permits more dynamic configurations, but is still pure.
-/
def Packager := (pkgDir : FilePath) → (args : List String) → PackageConfig

/--
  An alternate signature for package configurations
  that permits more dynamic configurations, including performing `IO`.
-/
def IOPackager := (pkgDir : FilePath) → (args : List String) → IO PackageConfig

namespace Package

/-- The package's `name` configuration. -/
def name (self : Package) : String :=
  self.config.name

/-- The package's `scripts` configuration. -/
def scripts (self : Package) : HashMap String Script :=
  self.config.scripts

/-- The package's `dependencies` configuration. -/
def dependencies (self : Package) : List Dependency :=
  self.config.dependencies

/-- The package's `extraDepTarget` configuration. -/
def extraDepTarget (self : Package) : OpaqueTarget :=
  self.config.extraDepTarget

/-- The package's `dir` joined with its `depsDir` configuration. -/
def depsDir (self : Package) : FilePath :=
  self.dir / self.config.depsDir

/-- The package's `dir` joined with its `srcDir` configuration. -/
def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir

/-- The package's root directory for Lean (i.e., `srcDir`). -/
def rootDir (self : Package) : FilePath :=
  self.srcDir

/-- The path to a module's `.lean` source file within the package. -/
def modToSrc (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.srcDir mod "lean"

/-- The package's `dir` joined with its `buildDir` configuration. -/
def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir

/-- The package's `buildDir` joined with its `oleanDir` configuration. -/
def oleanDir (self : Package) : FilePath :=
  self.buildDir / self.config.oleanDir

/-- The package's `leanArgs` configuration. -/
def leanArgs (self : Package) : Array String :=
  self.config.leanArgs

/-- The path to a module's `.olean` file within the package. -/
def modToOlean (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "olean"

/-- The path to module's `.hash` file within the package. -/
def modToHashFile (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "hash"

/-- The package's `libRoots` configuration. -/
def libRoots (self : Package) : Array Name :=
  self.config.libRoots

/-- The package's `libGlobs` configuration. -/
def libGlobs (self : Package) : Array Glob :=
  self.config.libGlobs

/-- Whether the given module is local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.libRoots.any fun root => root.isPrefixOf mod

/-- Get an `Array` of the package's module. -/
def getModuleArray (self : Package) : IO (Array Name) := do
  let mut mods := #[]
  for glob in self.libGlobs do
    mods ← glob.pushModules self.srcDir mods
  return mods

/-- The package's `leancArgs` configuration. -/
def leancArgs (self : Package) : Array String :=
  self.config.leancArgs

/-- The package's `buildDir` joined with its `irDir` configuration. -/
def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir

/-- To which Lake should output the package's `.c` files (.e., `irDir`). -/
def cDir (self : Package) : FilePath :=
  self.irDir

/-- The path to a module's `.c` file within the package. -/
def modToC (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.cDir mod "c"

/-- To which Lake should output the package's `.o` files (.e., `irDir`). -/
def oDir (self : Package) : FilePath :=
  self.irDir

/-- The path to a module's `.o` file within the package. -/
def modToO (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oDir mod "o"

/-- The package's `buildDir` joined with its `libDir` configuration. -/
def libDir (self : Package) : FilePath :=
  self.buildDir / self.config.libDir

/-- The package's `libName` configuration. -/
def staticLibName (self : Package) : FilePath :=
  self.config.libName

/-- The file name of package's static library (i.e., `lib{staticLibName}.a`) -/
def staticLibFileName (self : Package) : FilePath :=
  s!"lib{self.staticLibName}.a"

/-- The path to the package's static library. -/
def staticLibFile (self : Package) : FilePath :=
  self.libDir / self.staticLibFileName

/-- The package's `binRoot` configuration. -/
def binRoot (self : Package) : Name :=
  self.config.binRoot

/-- The package's `buildDir` joined with its `binDir` configuration. -/
def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir

/-- The package's `binName` configuration. -/
def binName (self : Package) : FilePath :=
  self.config.binName

/--
  The file name of package's binary executable
  (i.e., `binName` plus the platform's `exeExtension`).
-/
def binFileName (self : Package) : FilePath :=
  FilePath.withExtension self.binName FilePath.exeExtension

/-- The path to the package's executable. -/
def binFile (self : Package) : FilePath :=
  self.binDir / self.binFileName

/-- The package's `moreLibTargets` configuration. -/
def moreLibTargets (self : Package) : Array FileTarget :=
  self.config.moreLibTargets

/-- The package's `linkArgs` configuration. -/
def linkArgs (self : Package) : Array String :=
  self.config.linkArgs
