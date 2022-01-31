/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Std.Data.HashMap
import Lake.Build.TargetTypes
import Lake.Config.Glob
import Lake.Config.Opaque
import Lake.Config.WorkspaceConfig
import Lake.Config.Script

open Std System
open Lean (Name NameMap)

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

/-- The default setting for a `PackageConfig`'s `binRoot` option. -/
def defaultBinRoot : Name := `Main

--------------------------------------------------------------------------------
-- # Auxiliary Definitions and Helpers
--------------------------------------------------------------------------------

/--
The `src` of a `Dependency`.

In Lake, dependency sources currently come into flavors:
* Local `path`s relative to the package's directory.
* Remote `git` repositories that are download from a given `url`
  into the packages's `depsDir`.
-/
inductive Source where
| path (dir : FilePath)
| git (url rev : String)
deriving Inhabited, Repr

/-- A `Dependency` of a package. -/
structure Dependency where
  /--
  A `Name` for the dependency.
  The names of a package's dependencies cannot clash.
  -/
  name : Name
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

/- A buildable component of a `Package`. -/
inductive PackageFacet
| /-- The package's binary. -/ bin
| /-- The package's static library. -/ staticLib
| /-- The package's shared library. -/ sharedLib
| /-- The package's `.olean` files. -/ oleans
deriving BEq, DecidableEq, Repr
instance : Inhabited PackageFacet := ⟨PackageFacet.bin⟩

/-- Converts a snake case, kebab case, or lower camel case `String` to upper camel case. -/
def toUpperCamelCaseString (str : String) : String :=
  let parts := str.split fun chr => chr == '_' || chr == '-'
  String.join <| parts.map (·.capitalize)

/-- Converts a snake case, kebab case, or lower camel case `Name` to upper camel case. -/
def toUpperCamelCase (name : Name) : Name :=
  if let Name.str p s _ := name then
    Name.mkStr (toUpperCamelCase p) <| toUpperCamelCaseString s
  else
    name

--------------------------------------------------------------------------------
-- # PackageConfig
--------------------------------------------------------------------------------

/-- A `Package`'s declarative configuration. -/
structure PackageConfig extends WorkspaceConfig where

  /-- The `Name` of the package. -/
  name : Name

  /-
  An `Array` of the package's dependencies.
  See the documentation of `Dependency` for more information.
  -/
  dependencies : Array Dependency := #[]

  /--
  An extra `OpaqueTarget` that should be built before the package.

  `OpaqueTarget.collectList/collectArray` can be used combine multiple
  extra targets into a single `extraDepTarget`.
  -/
  extraDepTarget : OpaqueTarget := Target.nil

  /--
  The `PackageFacet` to build on a bare `lake build` of the package.
  Can be one of `bin`, `staticLib`, `sharedLib`, or `oleans`. Defaults to `bin`.
  See `lake help build` for more info on build facets.
  -/
  defaultFacet : PackageFacet := PackageFacet.bin

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
  Additional arguments to pass to `lean` while compiling Lean source files.
  -/
  moreLeanArgs : Array String := #[]

  /--
  Additional arguments to pass to `leanc`
  while compiling the C source files generated by `lean`.

  Lake already passes `-O3` and `-DNDEBUG` automatically,
  but you can change this by, for example, adding `-O0` and `-UNDEBUG`.
  -/
  moreLeancArgs : Array String := #[]

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
  local imports (i.e., fellow modules of the package).

  This setting is most useful for packages that are distributing both a
  library and a binary (like Lake itself). In such cases, it is common for
  there to be code (e.g., `main`) that is needed for the binary but should
  not be included in the library proper.
  -/
  binRoot : Name := defaultBinRoot

  /--
  Additional library `FileTarget`s (beyond the package's and its dependencies'
  libraries) to build and link to the package's binary executable (and/or to
  dependent package's executables).
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

  /--
  Additional arguments to pass to `leanc` while compiling the package's
  binary executable. These will come *after* the paths of libraries built
  with `moreLibTargets`.
  -/
  moreLinkArgs : Array String := #[]

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
  /--
  A `NameMap` of scripts for the package.

  A `Script` is a `(args : List String) → IO UInt32` definition with
  a `@[script]` tag that can be run by `lake run <script> [-- <args>]`.
  -/
  scripts : NameMap Script := {}
  deriving Inhabited

namespace OpaquePackage

unsafe def unsafeMk (pkg : Package) : OpaquePackage :=
  unsafeCast pkg

@[implementedBy unsafeMk] constant mk (pkg : Package) : OpaquePackage

instance : Coe Package OpaquePackage := ⟨mk⟩
instance : Inhabited OpaquePackage := ⟨mk Inhabited.default⟩

unsafe def unsafeGet (self : OpaquePackage) : Package :=
  unsafeCast self

@[implementedBy unsafeGet] constant get (self : OpaquePackage) : Package

instance : Coe OpaquePackage Package := ⟨get⟩

@[simp] axiom get_mk {pkg : Package} : get (mk pkg) = pkg

end OpaquePackage

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
def name (self : Package) : Name :=
  self.config.name

/-- The package's `dependencies` configuration. -/
def dependencies (self : Package) : Array Dependency :=
  self.config.dependencies

/-- The package's `extraDepTarget` configuration. -/
def extraDepTarget (self : Package) : OpaqueTarget :=
  self.config.extraDepTarget

/-- The package's `defaultFacet` configuration. -/
def defaultFacet (self : Package) : PackageFacet :=
   self.config.defaultFacet

/-- The package's `moreServerArgs` configuration. -/
def moreServerArgs (self : Package) : Array String :=
   self.config.moreServerArgs

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

/-- The package's `moreLeanArgs` configuration. -/
def moreLeanArgs (self : Package) : Array String :=
  self.config.moreLeanArgs

/-- The path to a module's `.olean` file within the package. -/
def modToOlean (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "olean"

/-- The path to a module's `.ilean` file within the package. -/
def modToIlean (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "ilean"

/-- The path to module's `.trace` file within the package. -/
def modToTraceFile (mod : Name) (self : Package) : FilePath :=
  Lean.modToFilePath self.oleanDir mod "trace"

/-- The package's `libRoots` configuration. -/
def libRoots (self : Package) : Array Name :=
  self.config.libRoots

/-- The package's `libGlobs` configuration. -/
def libGlobs (self : Package) : Array Glob :=
  self.config.libGlobs

/-- Whether the given module is considered local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.libRoots.any (fun root => root.isPrefixOf mod) ||
  self.libGlobs.any (fun glob => glob.matches mod)

/-- Get an `Array` of the package's module. -/
def getModuleArray (self : Package) : IO (Array Name) := do
  let mut mods := #[]
  for glob in self.libGlobs do
    mods ← glob.pushModules self.srcDir mods
  return mods

/- `-O3`, `-DNDEBUG`, and `moreLeancArgs` -/
def moreLeancArgs (self : Package) : Array String :=
  #["-O3", "-DNDEBUG"] ++ self.config.moreLeancArgs

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
def libName (self : Package) : FilePath :=
  self.config.libName

/-- The file name of package's static library (i.e., `lib{libName}.a`) -/
def staticLibFileName (self : Package) : FilePath :=
  s!"lib{self.libName}.a"

/-- The path to the package's static library. -/
def staticLibFile (self : Package) : FilePath :=
  self.libDir / self.staticLibFileName

/-- The package's `libName` configuration. -/
def self.sharedLibName (self : Package) : FilePath :=
  self.config.libName

/-- The file name of package's shared library. -/
def sharedLibFileName (self : Package) : FilePath :=
  s!"{self.libName}.{sharedLibExt}"

/-- The path to the package's shared library. -/
def sharedLibFile (self : Package) : FilePath :=
  self.libDir / self.sharedLibFileName

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

/-- The package's `supportInterpreter` configuration. -/
def supportInterpreter (self : Package) : Bool :=
  self.config.supportInterpreter

/-- `-rdynamic` (if non-Windows and `supportInterpreter`) plus `moreLinkArgs` -/
def moreLinkArgs (self : Package) : Array String :=
  if self.supportInterpreter && !Platform.isWindows then
    #["-rdynamic"] ++ self.config.moreLinkArgs
  else
    self.config.moreLinkArgs

/-- Whether the given module is in the package. -/
def hasModule (mod : Name) (self : Package) : Bool :=
  self.binRoot == mod || self.libGlobs.any fun glob => glob.matches mod
