/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Module

namespace Lake
open Lean System

/-- A Lean executable -- its package plus its configuration. -/
structure LeanExe where
  /-- The package the executable belongs to. -/
  pkg : Package
   /-- The executable's user-defined configuration. -/
  config : LeanExeConfig
  deriving Inhabited

/-- The Lean executable built into the package. -/
@[inline] def Package.builtinExe (self : Package) : LeanExe :=
  ⟨self, self.builtinExeConfig⟩

/-- Try to find a Lean executable in the package with the given name. -/
@[inline] def Package.findLeanExe? (name : Name) (self : Package) : Option LeanExe :=
  self.leanExeConfigs.find? name |>.map (⟨self, ·⟩)

namespace LeanExe

/-- The executable's root module. -/
@[inline] def root (self : LeanExe) : Module :=
  ⟨self.pkg, WfName.ofName self.config.root⟩

/--
The file name of binary executable
(i.e., `exeName` plus the platform's `exeExtension`).
-/
@[inline] def fileName (self : LeanExe) : FilePath :=
  FilePath.withExtension self.config.exeName FilePath.exeExtension

/-- The path to the executable in the package's `binDir`. -/
@[inline] def file (self : LeanExe) : FilePath :=
  self.pkg.binDir / self.fileName

/--
The arguments to pass to `leanc` when linking the binary executable.

That is, `-rdynamic` (if non-Windows and `supportInterpreter`) plus the
package's and then the executable's `moreLinkArgs`.
-/
def linkArgs (self : LeanExe) : Array String :=
  if self.config.supportInterpreter && !Platform.isWindows then
    #["-rdynamic"] ++ self.pkg.moreLinkArgs ++ self.config.moreLinkArgs
  else
    self.pkg.moreLinkArgs ++ self.config.moreLinkArgs
