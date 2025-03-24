/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Monad

/-! # Build Target Fetching
Utilities for fetching package, library, module, and executable targets and facets.
-/

namespace Lake
open Lean (Name)
open System (FilePath)

/-! ## Package Facets & Targets -/

/-- Fetch the build job of the specified package target. -/
def Package.fetchTargetJob
  (self : Package) (target : Name)
: FetchM OpaqueJob := do
  return (← fetch <| self.target target).toOpaque

/-- Fetch the build result of a target. -/
protected def TargetDecl.fetch
  (self : TargetDecl)
  [FamilyOut CustomData (self.pkg, self.name) α]
: FetchM (Job α) := do
  let some pkg ← findPackage? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  fetch <| pkg.target self.name

/-- Fetch the build job of the target. -/
def TargetDecl.fetchJob (self : TargetDecl) : FetchM OpaqueJob :=  do
  let some pkg ← findPackage? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  return (← fetch <| pkg.target self.name).toOpaque

/-- Fetch the build result of a package facet. -/
@[inline] protected def PackageFacetDecl.fetch
  (pkg : Package) (self : PackageFacetDecl) [FamilyOut PackageData self.name α]
: FetchM (Job α) := fetch <| pkg.facet self.name

/-- Fetch the build job of a package facet. -/
@[deprecated "Deprecated without replacement." (since := "2025-03-17")]
def PackageFacetConfig.fetchJob
  (pkg : Package) (self : PackageFacetConfig name)
: FetchM OpaqueJob := return (← fetch <| pkg.facet self.name).toOpaque

/-- Fetch the build job of a library facet. -/
def Package.fetchFacetJob
  (name : Name) (self : Package)
: FetchM OpaqueJob := do
  return  (← fetch <| self.facet name).toOpaque

/-! ## Module Facets -/

/-- Fetch the build result of a module facet. -/
@[inline] protected def ModuleFacetDecl.fetch
  (mod : Module) (self : ModuleFacetDecl) [FamilyOut ModuleData self.name α]
: FetchM (Job α) := fetch <| mod.facet self.name

/-- Fetch the build job of a module facet. -/
@[deprecated "Deprecated without replacement." (since := "2025-03-17")]
def ModuleFacetConfig.fetchJob
  (mod : Module) (self : ModuleFacetConfig name)
: FetchM OpaqueJob := return (← fetch <| mod.facet self.name).toOpaque

/-- Fetch the build job of a module facet. -/
def Module.fetchFacetJob (name : Name) (self : Module) : FetchM OpaqueJob :=
  return (← fetch <| self.facet name).toOpaque

/-! ## Lean Library Facets -/

/-- Get the Lean library in the workspace with the configuration's name. -/
@[inline] def LeanLibDecl.get
  (self : LeanLibDecl) [Monad m] [MonadError m] [MonadLake m] : m LeanLib
:= do
  let some lib ← findLeanLib? self.name
    | error s!"Lean library '{self.name}' does not exist in the workspace"
  return lib

/-- Fetch the build result of a library facet. -/
@[inline] protected def LibraryFacetDecl.fetch
  (lib : LeanLib) (self : LibraryFacetDecl) [FamilyOut LibraryData self.name α]
: FetchM (Job α) := fetch <| lib.facet self.name

/-- Fetch the build job of a library facet. -/
@[deprecated "Deprecated without replacement," (since := "2025-03-17")]
def LibraryFacetConfig.fetchJob
  (lib : LeanLib) (self : LibraryFacetConfig name)
: FetchM OpaqueJob := return (← fetch <| lib.facet self.name).toOpaque

/-- Fetch the build job of a library facet. -/
def LeanLib.fetchFacetJob
  (name : Name) (self : LeanLib)
: FetchM OpaqueJob := return (← fetch <| self.facet name).toOpaque

/-! ## Lean Executable Target -/

/-- Get the Lean executable in the workspace with the configuration's name. -/
@[inline] def LeanExeDecl.get
  (self : LeanExeDecl) [Monad m] [MonadError m] [MonadLake m]
: m LeanExe := do
  let some exe ← findLeanExe? self.name
    | error s!"Lean executable '{self.name}' does not exist in the workspace"
  return exe

/-- Fetch the build of the Lean executable. -/
@[inline] def LeanExeDecl.fetch (self : LeanExeDecl) : FetchM (Job FilePath) := do
  (← self.get).exe.fetch

/-- Fetch the build of the Lean executable. -/
@[inline] def LeanExe.fetch (self : LeanExe) : FetchM (Job FilePath) :=
  self.exe.fetch
