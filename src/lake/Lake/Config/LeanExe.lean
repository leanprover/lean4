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

/-- The Lean executables of the package (as an Array). -/
@[inline] def Package.leanExes (self : Package) : Array LeanExe :=
  self.leanExeConfigs.foldl (fun a v => a.push ⟨self, v⟩) #[]

/-- Try to find a Lean executable in the package with the given name. -/
@[inline] def Package.findLeanExe? (name : Name) (self : Package) : Option LeanExe :=
  self.leanExeConfigs.find? name |>.map (⟨self, ·⟩)

/--
Converts the executable configuration into a library
with a single module (the root).
-/
def LeanExeConfig.toLeanLibConfig (self : LeanExeConfig) : LeanLibConfig where
  name := self.name
  srcDir := self.srcDir
  roots := #[]
  libName := self.exeName
  extraDepTargets := self.extraDepTargets
  nativeFacets := self.nativeFacets
  toLeanConfig := self.toLeanConfig

namespace LeanExe

/-- The executable's well-formed name. -/
@[inline] def name (self : LeanExe) : Name :=
  self.config.name

/-- Converts the executable into a library with a single module (the root). -/
@[inline] def toLeanLib (self : LeanExe) : LeanLib :=
  ⟨self.pkg, self.config.toLeanLibConfig⟩

/-- The executable's root module. -/
@[inline] def root (self : LeanExe) : Module where
  lib := self.toLeanLib
  name := self.config.root
  keyName := self.pkg.name ++ self.config.root

/-- Return the the root module if the name matches, otherwise return none. -/
def isRoot? (name : Name) (self : LeanExe) : Option Module :=
  if name == self.config.root then some self.root else none

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


/--
The arguments to weakly pass to `leanc` when linking the binary executable.
That is, the package's `weakLinkArgs` plus the executable's  `weakLinkArgs`.
-/
@[inline] def weakLinkArgs (self : LeanExe) : Array String :=
  self.pkg.weakLinkArgs ++ self.config.weakLinkArgs

end LeanExe

/-- Locate the named, buildable, but not necessarily importable, module in the package. -/
def Package.findTargetModule? (mod : Name) (self : Package) : Option Module :=
  self.leanExes.findSomeRev? (·.isRoot? mod) <|> self.findModule? mod
