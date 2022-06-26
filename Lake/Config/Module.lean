/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Trace
import Lake.Config.Package
import Lake.Util.Name

namespace Lake
open Std System

/-- A buildable Lean module of a `Package`. -/
structure Module where
  pkg : Package
  name : WfName
  deriving Inhabited

abbrev ModuleSet := RBTree Module (·.name.quickCmp ·.name)
@[inline] def ModuleSet.empty : ModuleSet := RBTree.empty

abbrev ModuleMap (α) := RBMap Module α (·.name.quickCmp ·.name)
@[inline] def ModuleMap.empty : ModuleMap α := RBMap.empty

/-- Locate the named module in the package (if it is local to it). -/
def Package.findModule? (mod : Name) (self : Package) : Option Module :=
  let mod := WfName.ofName mod
  if self.isBuildableModule mod then some ⟨self, mod⟩ else none

namespace Module

@[inline] def leanFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.srcDir self.name "lean"

@[inline] def oleanFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.oleanDir self.name "olean"

@[inline] def ileanFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.oleanDir self.name "ilean"

@[inline] def traceFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.oleanDir self.name "trace"

@[inline] def cFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.irDir self.name "c"

@[inline] def cTraceFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.irDir self.name "c.trace"

@[inline] def oFile (self : Module) : FilePath :=
  Lean.modToFilePath self.pkg.irDir self.name "o"

@[inline] def dynlib (self : Module) : FilePath :=
  -- NOTE: file name MUST be unique on Windows
  self.name.toStringWithSep "-"

@[inline] def dynlibFile (self : Module) : FilePath :=
  self.pkg.libDir / s!"lib{self.dynlib}.{sharedLibExt}"

@[inline] def leanArgs (self : Module) : Array String :=
  self.pkg.moreLeanArgs

@[inline] def leancArgs (self : Module) : Array String :=
  self.pkg.moreLeancArgs

@[inline] def linkArgs (self : Module) : Array String :=
  -- TODO: derive link arguments from library, not package
  self.pkg.config.moreLinkArgs

@[inline] def shouldPrecompile (self : Module) : Bool :=
  self.pkg.precompileModules

@[inline] def isLeanOnly (self : Module) : Bool :=
  self.pkg.isLeanOnly && !self.shouldPrecompile

-- ## Trace Helpers

protected def getMTime (self : Module) : IO MTime := do
  return mixTrace (← getMTime self.oleanFile) (← getMTime self.ileanFile)

instance : GetMTime Module := ⟨Module.getMTime⟩

protected def computeHash (self : Module) : IO Hash := do
  return mixTrace (← computeHash self.oleanFile) (← computeHash self.ileanFile)

instance : ComputeHash Module IO := ⟨Module.computeHash⟩

protected def checkExists (self : Module) : BaseIO Bool := do
  return (← checkExists self.oleanFile) && (← checkExists self.ileanFile)

instance : CheckExists Module := ⟨Module.checkExists⟩
