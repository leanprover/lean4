/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Monad
public import Lake.Config.InputFile
import Lake.Build.Infos

/-! # Build Target Fetching
Utilities for fetching package, library, module, and executable targets and facets.
-/

open Lean (Name)
open System (FilePath)

namespace Lake

/-- Get the target in the workspace corresponding to this configuration. -/
@[inline] public def KConfigDecl.get
  [Monad m] [MonadError m] [MonadLake m] (self : KConfigDecl kind)
: m (ConfigTarget kind) := do
  let some pkg ← findPackageByKey? self.pkg
    | error s!"package of target '{self.pkg}/{self.name}' not found in workspace"
  let config := cast (by rw [self.kind_eq, pkg.keyName_eq]) self.config
  return ConfigTarget.mk pkg self.name config

/-! ## Package Facets & Targets -/

/-- Fetch the build job of the specified package target. -/
public def Package.fetchTargetJob
  (self : Package) (target : Name)
: FetchM OpaqueJob := do
  return (← fetch <| self.target target).toOpaque

/-- Fetch the build result of a target. -/
public protected def TargetDecl.fetch
  (self : TargetDecl) [FamilyOut (CustomData self.pkg) self.name α]
: FetchM (Job α) := do
  let some pkg ← findPackageByKey? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  fetch <| pkg.target self.name

/-- Fetch the build job of the target. -/
public def TargetDecl.fetchJob (self : TargetDecl) : FetchM OpaqueJob :=  do
  let some pkg ← findPackageByKey? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  return (← (pkg.target self.name).fetch).toOpaque

/-- Fetch the build result of a package facet. -/
@[inline] public protected def PackageFacetDecl.fetch
  (pkg : Package) (self : PackageFacetDecl) [FamilyOut FacetOut self.name α]
: FetchM (Job α) := fetch <| pkg.facetCore self.name

/-- Fetch the build job of a library facet. -/
public def Package.fetchFacetJob
  (name : Name) (self : Package)
: FetchM OpaqueJob := do
  return  (← fetch <| self.facet name).toOpaque

/-! ## Module Facets -/

/-- Fetch the build result of a module facet. -/
@[inline] public protected def ModuleFacetDecl.fetch
  (mod : Module) (self : ModuleFacetDecl) [FamilyOut FacetOut self.name α]
: FetchM (Job α) := fetch <| mod.facetCore self.name

/-- Fetch the build job of a module facet. -/
public def Module.fetchFacetJob (name : Name) (self : Module) : FetchM OpaqueJob :=
  return (← fetch <| self.facet name).toOpaque

/-! ## Lean Library Facets -/

/-- Get the Lean library in the workspace corresponding to this configuration. -/
@[inline] public def LeanLibDecl.get
  (self : LeanLibDecl) [Monad m] [MonadError m] [MonadLake m] : m LeanLib
:= KConfigDecl.get self

/-- Fetch the build result of a library facet. -/
@[inline] public protected def LibraryFacetDecl.fetch
  (lib : LeanLib) (self : LibraryFacetDecl) [FamilyOut FacetOut self.name α]
: FetchM (Job α) := fetch <| lib.facetCore self.name

/-- Fetch the build job of a library facet. -/
public def LeanLib.fetchFacetJob
  (name : Name) (self : LeanLib)
: FetchM OpaqueJob := return (← fetch <| self.facet name).toOpaque

/-! ## Lean Executable Target -/

/-- Get the Lean executable in the workspace corresponding to this configuration. -/
@[inline] public def LeanExeDecl.get
  (self : LeanExeDecl) [Monad m] [MonadError m] [MonadLake m] : m LeanExe
:= KConfigDecl.get self

/-- Fetch the build of the Lean executable. -/
@[inline] public def LeanExe.fetch (self : LeanExe) : FetchM (Job FilePath) :=
  self.exe.fetch

/-- Fetch the build of the Lean executable. -/
@[inline] public def LeanExeDecl.fetch (self : LeanExeDecl) : FetchM (Job FilePath) := do
  (← self.get).fetch

/-! ## Input File / Directory Targets -/

/-- Fetch the input file. -/
@[inline] public def InputFile.fetch (self : InputFile) : FetchM (Job FilePath) :=
  self.default.fetch

/-- Get the input file in the workspace corresponding to this configuration. -/
@[inline] public def InputFileDecl.get
  (self : InputFileDecl) [Monad m] [MonadError m] [MonadLake m] : m InputFile
:= KConfigDecl.get self

/-- Fetch the input file. -/
@[inline] public def InputFileDecl.fetch (self : InputFileDecl) : FetchM (Job FilePath) := do
  (← self.get).default.fetch

/-- Fetch the files in the input directory. -/
@[inline] public def InputDir.fetch (self : InputDir) : FetchM (Job (Array FilePath)) :=
  self.default.fetch

/-- Get the input directory in the workspace corresponding to this configuration. -/
@[inline] public def InputDirDecl.get
  (self : InputDirDecl) [Monad m] [MonadError m] [MonadLake m] : m InputDir
:= KConfigDecl.get self

/-- Fetch the files in the input directory. -/
@[inline] public def InputDirDecl.fetch (self : InputDirDecl) : FetchM (Job (Array FilePath)) := do
  (← self.get).default.fetch
