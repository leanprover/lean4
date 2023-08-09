/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Monad

/-! # Build Target Fetching
Utilities for fetching package, library, module, and executable targets and facets.
-/

namespace Lake

/-! ## Package Facets & Targets -/

/-- Fetch the build job of the specified package target. -/
def Package.fetchTargetJob (self : Package)
(target : Name) : IndexBuildM (BuildJob Unit) :=  do
  let some config := self.findTargetConfig? target
    | error s!"package '{self.name}' has no target '{target}'"
  return config.getJob (← fetch <| self.target target)

/-- Fetch the build result of a target. -/
protected def TargetDecl.fetch (self : TargetDecl)
[FamilyOut CustomData (self.pkg, self.name) α] : IndexBuildM α := do
  let some pkg ← findPackage? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  fetch <| pkg.target self.name

/-- Fetch the build job of the target. -/
def TargetDecl.fetchJob (self : TargetDecl) : IndexBuildM (BuildJob Unit) :=  do
  let some pkg ← findPackage? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  return self.config.getJob (← fetch <| pkg.target self.name)

/-- Fetch the build result of a package facet. -/
@[inline] protected def PackageFacetDecl.fetch (pkg : Package)
(self : PackageFacetDecl) [FamilyOut PackageData self.name α] : IndexBuildM α := do
  fetch <| pkg.facet self.name

/-- Fetch the build job of a package facet. -/
def PackageFacetConfig.fetchJob (pkg : Package)
(self : PackageFacetConfig name) : IndexBuildM (BuildJob Unit) :=  do
  let some getJob := self.getJob?
    | error s!"package facet '{name}' has no associated build job"
  return getJob <| ← fetch <| pkg.facet self.name

/-- Fetch the build job of a library facet. -/
def Package.fetchFacetJob (name : Name)
(self : Package) : IndexBuildM (BuildJob Unit) :=  do
  let some config := (← getWorkspace).packageFacetConfigs.find? name
    | error s!"package facet '{name}' does not exist in workspace"
  inline <| config.fetchJob self

/-! ## Module Facets -/

/-- Fetch the build result of a module facet. -/
@[inline] protected def ModuleFacetDecl.fetch (mod : Module)
(self : ModuleFacetDecl) [FamilyOut ModuleData self.name α] : IndexBuildM α := do
  fetch <| mod.facet self.name

/-- Fetch the build job of a module facet. -/
def ModuleFacetConfig.fetchJob (mod : Module)
(self : ModuleFacetConfig name) : IndexBuildM (BuildJob Unit) :=  do
  let some getJob := self.getJob?
    | error "module facet '{self.name}' has no associated build job"
  return getJob <| ← fetch <| mod.facet self.name

/-- Fetch the build job of a module facet. -/
def Module.fetchFacetJob
(name : Name) (self : Module) : IndexBuildM (BuildJob Unit) :=  do
  let some config := (← getWorkspace).moduleFacetConfigs.find? name
    | error "library facet '{name}' does not exist in workspace"
  inline <| config.fetchJob self

/-! ## Lean Library Facets -/

/-- Get the Lean library in the workspace with the configuration's name. -/
@[inline] def LeanLibConfig.get
(self : LeanLibConfig) [Monad m] [MonadError m] [MonadLake m] : m LeanLib := do
  let some lib ← findLeanLib? self.name
    | error "Lean library '{self.name}' does not exist in the workspace"
  return lib

/-- Fetch the build result of a library facet. -/
@[inline] protected def LibraryFacetDecl.fetch (lib : LeanLib)
(self : LibraryFacetDecl) [FamilyOut LibraryData self.name α] : IndexBuildM α := do
  fetch <| lib.facet self.name

/-- Fetch the build job of a library facet. -/
def LibraryFacetConfig.fetchJob (lib : LeanLib)
(self : LibraryFacetConfig name) : IndexBuildM (BuildJob Unit) :=  do
  let some getJob := self.getJob?
    | error "library facet '{self.name}' has no associated build job"
  return getJob <| ← fetch <| lib.facet self.name

/-- Fetch the build job of a library facet. -/
def LeanLib.fetchFacetJob (name : Name)
(self : LeanLib) : IndexBuildM (BuildJob Unit) :=  do
  let some config := (← getWorkspace).libraryFacetConfigs.find? name
    | error "library facet '{name}' does not exist in workspace"
  inline <| config.fetchJob self

/-! ## Lean Executable Target -/

/-- Get the Lean executable in the workspace with the configuration's name. -/
@[inline] def LeanExeConfig.get (self : LeanExeConfig)
[Monad m] [MonadError m] [MonadLake m] : m LeanExe := do
  let some exe ← findLeanExe? self.name
    | error "Lean executable '{self.name}' does not exist in the workspace"
  return exe

/-- Fetch the build of the Lean executable. -/
@[inline] def LeanExeConfig.fetch
(self : LeanExeConfig) : IndexBuildM (BuildJob FilePath) := do
  (← self.get).exe.fetch
