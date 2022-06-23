/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Name
import Lake.Util.String
import Lake.Build.TargetTypes
import Lake.Config.Glob
import Lake.Config.Opaque
import Lake.Config.WorkspaceConfig
import Lake.Config.Targets
import Lake.Config.Dependency
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
-- # PackageFacet
--------------------------------------------------------------------------------

/- A buildable component of a `Package`. -/
inductive PackageFacet
| /-- The package's binary executable. -/ exe
| /-- The package's binary executable. **DEPRECATED:** Use `exe` instead. -/ bin
| /-- The package's static library. -/ staticLib
| /-- The package's shared library. -/ sharedLib
| /-- The package's lean library (e.g. `olean` / `ilean` files). -/ leanLib
| /-- The package's `.olean` files. **DEPRECATED:** Use `leanLib` instead. -/ oleans
| /-- The package has no buildable component. -/ none
deriving BEq, DecidableEq, Repr
instance : Inhabited PackageFacet := ⟨PackageFacet.exe⟩

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

  **DEPRECATED:**
  This setting will be removed in a future version of Lake.
  Use the `require` syntax to declare dependencies instead.
  -/
  dependencies : Array Dependency := #[]

  /--
  An extra `OpaqueTarget` that should be built before the package.

  `OpaqueTarget.collectList/collectArray` can be used combine multiple
  extra targets into a single `extraDepTarget`.
  -/
  extraDepTarget : OpaqueTarget := Target.nil

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
  Whether to compile each module into a native shared library that is loaded
  whenever the module is imported. This speeds up evaluation of metaprograms
  and enables the interpreter to run functions marked `@[extern]`.

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

  /--
  Additional arguments to pass to `leanc` while compiling the package's
  binary executable. These will come *after* the paths of libraries built
  with `moreLibTargets`.
  -/
  moreLinkArgs : Array String := #[]

  /--
  Marks the package as only containing scripts.

  Used to turn off deprecation warnings about package facets in packages
  not intended to have any targets.
  -/
  scriptsOnly : Bool := false

deriving Inhabited

namespace PackageConfig

/-- The configuration of the package's library. -/
def toLeanLibConfig (self : PackageConfig) : LeanLibConfig where
  name := self.libName
  roots := self.libRoots
  globs := self.libGlobs

/-- The configuration of the package's binary executable. -/
def toLeanExeConfig (self : PackageConfig) : LeanExeConfig where
  root := self.binRoot
  name := self.binName
  supportInterpreter := self.supportInterpreter
  moreLinkArgs := self.moreLinkArgs

end PackageConfig

--------------------------------------------------------------------------------
-- # Package
--------------------------------------------------------------------------------

/-- A Lake package -- its location plus its configuration. -/
structure Package where
  /-- The path to the package's directory. -/
  dir : FilePath
  /-- The package's configuration. -/
  config : PackageConfig
  /-- The package's well-formed name. -/
  name : WfName := WfName.ofName config.name
  /-- Scripts for the package. -/
  scripts : NameMap Script := {}
  /-- Lean library targets for the package. -/
  leanLibs : NameMap LeanLibConfig := {}
  /-- Lean binary executable targets for the package. -/
  leanExes : NameMap LeanExeConfig := {}
   /-- External library targets for the package. -/
  externLibs : NameMap ExternLibConfig := {}
  /--
  The names of the package's targets to build by default
  (i.e., on a bare `lake build` of the package).
  -/
  defaultTargets : Array Name := #[]
  deriving Inhabited

namespace OpaquePackage

unsafe def unsafeMk (pkg : Package) : OpaquePackage :=
  unsafeCast pkg

@[implementedBy unsafeMk] opaque mk (pkg : Package) : OpaquePackage

instance : Coe Package OpaquePackage := ⟨mk⟩
instance : Inhabited OpaquePackage := ⟨mk Inhabited.default⟩

unsafe def unsafeGet (self : OpaquePackage) : Package :=
  unsafeCast self

@[implementedBy unsafeGet] opaque get (self : OpaquePackage) : Package

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

/-- The package's `dependencies` configuration. -/
def dependencies (self : Package) : Array Dependency :=
  self.config.dependencies

/-- The package's `extraDepTarget` configuration. -/
def extraDepTarget (self : Package) : OpaqueTarget :=
  self.config.extraDepTarget

/-- The package's `defaultFacet` configuration. -/
def defaultFacet (self : Package) : PackageFacet :=
   self.config.defaultFacet

/-- Get the package's library configuration with the given name. -/
def findLeanLib? (name : Name) (self : Package) : Option LeanLibConfig :=
  self.leanLibs.find? name

/-- Get the package's executable configuration with the given name. -/
def findLeanExe? (name : Name) (self : Package) : Option LeanExeConfig :=
  self.leanExes.find? name

/-- Get the package's external library target with the given name. -/
def findExternLib? (name : Name) (self : Package) : Option ExternLibConfig :=
  self.externLibs.find? name

/-- Get an `Array` of the package's external library targets. -/
def externLibTargets (self : Package) : Array FileTarget :=
  self.externLibs.fold (fun xs _ x => xs.push x.target) #[] ++
  self.config.moreLibTargets

/-- The package's `precompileModules` configuration. -/
def precompileModules (self : Package) : Bool :=
  self.config.precompileModules

/-- The package's `moreServerArgs` configuration. -/
def moreServerArgs (self : Package) : Array String :=
  self.config.moreServerArgs

/-- The package's `dir` joined with its `srcDir` configuration. -/
def srcDir (self : Package) : FilePath :=
  self.dir / self.config.srcDir

/-- The package's root directory for `lean` (i.e., `srcDir`). -/
def rootDir (self : Package) : FilePath :=
  self.srcDir

/-- The package's `dir` joined with its `buildDir` configuration. -/
def buildDir (self : Package) : FilePath :=
  self.dir / self.config.buildDir

/-- The package's `buildDir` joined with its `oleanDir` configuration. -/
def oleanDir (self : Package) : FilePath :=
  self.buildDir / self.config.oleanDir

/-- The package's `moreLeanArgs` configuration. -/
def moreLeanArgs (self : Package) : Array String :=
  self.config.moreLeanArgs

/- `-O3`, `-DNDEBUG`, and `moreLeancArgs` -/
def moreLeancArgs (self : Package) : Array String :=
  #["-O3", "-DNDEBUG"] ++ self.config.moreLeancArgs

/-- The package's `buildDir` joined with its `irDir` configuration. -/
def irDir (self : Package) : FilePath :=
  self.buildDir / self.config.irDir

/-- The package's `buildDir` joined with its `libDir` configuration. -/
def libDir (self : Package) : FilePath :=
  self.buildDir / self.config.libDir

/-- The package's `buildDir` joined with its `binDir` configuration. -/
def binDir (self : Package) : FilePath :=
  self.buildDir / self.config.binDir

/-- The library configuration built into the package configuration. -/
def builtinLibConfig (self : Package) : LeanLibConfig :=
  self.config.toLeanLibConfig

/-- The binary executable configuration built into the package configuration. -/
def builtinExeConfig (self : Package) : LeanExeConfig :=
  self.config.toLeanExeConfig

/-- Get an `Array` of the package's modules. -/
def getModuleArray (self : Package) : IO (Array Name) :=
  self.builtinLibConfig.getModuleArray self.srcDir

/-- Whether the given module is considered local to the package. -/
def isLocalModule (mod : Name) (self : Package) : Bool :=
  self.leanLibs.any (fun _ lib => lib.isLocalModule mod) ||
  self.builtinLibConfig.isLocalModule mod

/-- Whether the given module is in the package (i.e., can build it). -/
def isBuildableModule (mod : Name) (self : Package) : Bool :=
  self.leanLibs.any (fun _ lib => lib.isBuildableModule mod) ||
  self.leanExes.any (fun _ exe => exe.root == mod) ||
  self.builtinLibConfig.isBuildableModule mod ||
  self.config.binRoot == mod
