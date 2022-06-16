/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.String
import Lake.Build.TargetTypes
import Lake.Config.Glob

namespace Lake
open Lean System

--------------------------------------------------------------------------------
-- # Lean Library Build Configuration
--------------------------------------------------------------------------------

/-- A Lean library's declarative configuration. -/
structure LeanLibConfig where
  /-- The name of the target. -/
  name : Name

  /--
  The root module(s) of the library.

  Submodules of these roots (e.g., `Lib.Foo` of `Lib`) are considered
  part of the package.

  Defaults to a single root of the library's upper camel case name.
  -/
  roots : Array Name := #[toUpperCamelCase name]

  /--
  An `Array` of module `Glob`s to build for the library.
  Defaults to a `Glob.one` of each of the library's  `roots`.

  Submodule globs build every source file within their directory.
  Local imports of glob'ed files (i.e., fellow modules of the workspace) are
  also recursively built.
  -/
  globs : Array Glob := roots.map Glob.one

  /--
  The name of the library.
  Used as a base for the file names of its static and dynamic binaries.
  Defaults to the upper camel case name of the target.
  -/
  libName := toUpperCamelCase name |>.toString (escape := false)

  /--
  Additional arguments to pass to `leanc` while linking the shared library.
  These will come *after* the paths of package's external libraries.
  -/
  moreLinkArgs : Array String := #[]

deriving Inhabited, Repr

namespace LeanLibConfig

/-- Whether the given module is considered local to the library. -/
def isLocalModule (mod : Name) (self : LeanLibConfig) : Bool :=
  self.roots.any (fun root => root.isPrefixOf mod) ||
  self.globs.any (fun glob => glob.matches mod)

/-- Whether the given module is a buildable part of the library. -/
def isBuildableModule (mod : Name) (self : LeanLibConfig) : Bool :=
  self.globs.any (fun glob => glob.matches mod) ||
  self.roots.any (fun root => root.isPrefixOf mod && self.globs.any (·.matches root))

/-- Get an `Array` of the library's modules. -/
def getModuleArray (self : LeanLibConfig) (srcDir : FilePath) : IO (Array Name) := do
  let mut mods := #[]
  for glob in self.globs do
    mods ← glob.pushModules srcDir mods
  return mods

/-- The file name of package's static library (i.e., `lib{libName}.a`) -/
def staticLibFileName (self : LeanLibConfig) : FilePath :=
  s!"lib{self.libName}.a"

/-- The file name of package's shared library. -/
def sharedLibFileName (self : LeanLibConfig) : FilePath :=
  s!"{self.libName}.{sharedLibExt}"

/--
The arguments to pass to `leanc` when linking the shared library.
Just `moreLinkArgs`.
-/
def linkArgs (self : LeanLibConfig) : Array String :=
  self.moreLinkArgs

end LeanLibConfig

--------------------------------------------------------------------------------
-- # Lean Executable Build Configuration
--------------------------------------------------------------------------------

/-- A Lean executable's declarative configuration. -/
structure LeanExeConfig where
  /-- The name of the target. -/
  name : Name

  /--
  The root module of the binary executable.
  Should include a `main` definition that will serve
  as the entry point of the program.

  The root is built by recursively building its
  local imports (i.e., fellow modules of the workspace).

  Defaults to the name of the target.
  -/
  root : Name := name

  /--
  The name of the binary executable.
  Defaults to the target name with any `.` replaced with a `-`.
  -/
  exeName : String := name.toStringWithSep "-" (escape := false)

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
  Additional arguments to pass to `leanc` when linking the binary executable.
  These will come *after* the paths of the package's external libraries.
  -/
  moreLinkArgs : Array String := #[]

deriving Inhabited, Repr

namespace LeanExeConfig

/--
The file name of binary executable
(i.e., `exeName` plus the platform's `exeExtension`).
-/
def fileName (self : LeanExeConfig) : FilePath :=
  FilePath.withExtension self.exeName FilePath.exeExtension

/--
The arguments to pass to `leanc` when linking the binary executable.
`-rdynamic` (if non-Windows and `supportInterpreter`) plus `moreLinkArgs`.
-/
def linkArgs (self : LeanExeConfig) : Array String :=
  if self.supportInterpreter && !Platform.isWindows then
    #["-rdynamic"] ++ self.moreLinkArgs
  else
    self.moreLinkArgs

end LeanExeConfig

--------------------------------------------------------------------------------
-- # External Library Build Configuration
--------------------------------------------------------------------------------

/-- A external library's declarative configuration. -/
structure ExternLibConfig where
  /-- The name of the target. -/
  name : Name

  /-- The library's build target. -/
  target : FileTarget

deriving Inhabited
