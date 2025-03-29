/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Module

namespace Lake
open Lean System

/-- A Lean executable -- its package plus its configuration. -/
abbrev LeanExe := ConfigTarget LeanExe.configKind

/-- The Lean executables of the package (as an Array). -/
@[inline] def Package.leanExes (self : Package) : Array LeanExe :=
  self.configTargets LeanExe.configKind

/-- Try to find a Lean executable in the package with the given name. -/
@[inline] def Package.findLeanExe? (name : Name) (self : Package) : Option LeanExe :=
  self.findConfigTarget? LeanExe.configKind name

/--
Converts the executable configuration into a library
with a single module (the root).
-/
def LeanExeConfig.toLeanLibConfig (self : LeanExeConfig n) : LeanLibConfig n where
  srcDir := self.srcDir
  roots := #[]
  libName := self.exeName
  needs := self.needs
  extraDepTargets := self.extraDepTargets
  nativeFacets := self.nativeFacets
  toLeanConfig := self.toLeanConfig

namespace LeanExe

/-- The executable's user-defined configuration. -/
@[inline] nonrec def config (self : LeanExe) : LeanExeConfig self.name :=
  self.config

/-- Converts the executable into a library with a single module (the root). -/
@[inline] def toLeanLib (self : LeanExe) : LeanLib :=
  ⟨self.pkg, self.name, self.config.toLeanLibConfig⟩

/-- The executable's root module. -/
@[inline] def root (self : LeanExe) : Module where
  lib := self.toLeanLib
  name := self.config.root
  keyName := self.pkg.name ++ self.config.root

/-- Return the root module if the name matches, otherwise return none. -/
def isRoot? (name : Name) (self : LeanExe) : Option Module :=
  if name == self.config.root then some self.root else none

/--
The file name of binary executable
(i.e., `exeName` plus the platform's `exeExtension`).
-/
@[inline] def fileName (self : LeanExe) : FilePath :=
  FilePath.addExtension self.config.exeName FilePath.exeExtension

/-- The path to the executable in the package's `binDir`. -/
@[inline] def file (self : LeanExe) : FilePath :=
  self.pkg.binDir / self.fileName

/-- The executable's `supportInterpreter` configuration. -/
@[inline] def supportInterpreter (self : LeanExe) : Bool :=
  self.config.supportInterpreter

/--
The arguments to pass to `leanc` when linking the binary executable.

By default, the package's plus the executable's `moreLinkArgs`.
If `supportInterpreter := true`, Lake prepends `-rdynamic` on non-Windows
systems.
-/
def linkArgs (self : LeanExe) : Array String :=
  if self.config.supportInterpreter && !Platform.isWindows then
    #["-rdynamic"] ++ self.pkg.moreLinkArgs ++ self.config.moreLinkArgs
  else
    self.pkg.moreLinkArgs ++ self.config.moreLinkArgs

/--
Whether the Lean shared library should be dynamically linked to the executable.

If `supportInterpreter := true`, Lean symbols must be visible to the
interpreter. On Windows, it is not possible to statically include these
symbols in the executable due to symbol limits, so Lake dynamically links to
the Lean shared library. Otherwise, Lean is linked statically.
-/
@[inline] def sharedLean (self : LeanExe) : Bool :=
  strictAnd Platform.isWindows self.config.supportInterpreter

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
