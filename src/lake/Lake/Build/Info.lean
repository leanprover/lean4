/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.LeanExe
import Lake.Config.ExternLib
import Lake.Build.Facets

/-!
# Build Info

This module defines the Lake build info type and related utilities.
Build info is what is the data passed to a Lake build function to facilitate
the build.
-/

namespace Lake
open Lean (Name)

/-- The type of Lake's build info. -/
inductive BuildInfo
| moduleFacet (module : Module) (facet : Name)
| packageFacet (package : Package) (facet : Name)
| libraryFacet (lib : LeanLib) (facet : Name)
| leanExe (exe : LeanExe)
| staticExternLib (lib : ExternLib)
| sharedExternLib (lib : ExternLib)
| dynlibExternLib (lib : ExternLib)
| target (package : Package) (target : Name)

--------------------------------------------------------------------------------
/-! ## Build Info & Keys                                                      -/
--------------------------------------------------------------------------------

/-! ### Build Key Helper Constructors -/

abbrev Module.facetBuildKey (facet : Name) (self : Module) : BuildKey :=
  .moduleFacet self.keyName facet

abbrev Package.facetBuildKey (facet : Name) (self : Package) : BuildKey :=
  .packageFacet self.name facet

abbrev Package.targetBuildKey (target : Name) (self : Package) : BuildKey :=
  .customTarget self.name target

abbrev LeanLib.facetBuildKey (self : LeanLib) (facet : Name) : BuildKey :=
  .targetFacet self.pkg.name self.name (`leanLib ++ facet)

abbrev LeanExe.buildKey (self : LeanExe) : BuildKey :=
  .targetFacet self.pkg.name self.name exeFacet

abbrev ExternLib.staticBuildKey (self : ExternLib) : BuildKey :=
  .targetFacet self.pkg.name self.name staticFacet

abbrev ExternLib.sharedBuildKey (self : ExternLib) : BuildKey :=
  .targetFacet self.pkg.name self.name sharedFacet

abbrev ExternLib.dynlibBuildKey (self : ExternLib) : BuildKey :=
  .targetFacet self.pkg.name self.name dynlibFacet

/-! ### Build Info to Key -/

/-- The key that identifies the build in the Lake build store. -/
@[reducible] def BuildInfo.key : (self : BuildInfo) → BuildKey
| moduleFacet m f => m.facetBuildKey f
| packageFacet p f => p.facetBuildKey f
| libraryFacet l f => l.facetBuildKey f
| leanExe x => x.buildKey
| staticExternLib l => l.staticBuildKey
| sharedExternLib l => l.sharedBuildKey
| dynlibExternLib l => l.dynlibBuildKey
| target p t => p.targetBuildKey t

/-! ### Instances for deducing data types of `BuildInfo` keys -/

instance [FamilyOut ModuleData f α]
: FamilyDef BuildData (BuildInfo.key (.moduleFacet m f)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyOut PackageData f α]
: FamilyDef BuildData (BuildInfo.key (.packageFacet p f)) α where
  family_key_eq_type := by unfold BuildData; simp

instance (priority := low) {p : NPackage n} : FamilyDef BuildData
  (.customTarget p.toPackage.name t) (CustomData (n,t)) := ⟨by simp⟩

instance {p : NPackage n} [FamilyOut CustomData (n, t) α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyOut TargetData (`leanLib ++ f) α]
: FamilyDef BuildData (BuildInfo.key (.libraryFacet l f)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyOut TargetData LeanExe.exeFacet α]
: FamilyDef BuildData (BuildInfo.key (.leanExe x)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyOut TargetData ExternLib.staticFacet α]
: FamilyDef BuildData (BuildInfo.key (.staticExternLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyOut TargetData ExternLib.sharedFacet α]
: FamilyDef BuildData (BuildInfo.key (.sharedExternLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

instance [FamilyOut TargetData ExternLib.dynlibFacet α]
: FamilyDef BuildData (BuildInfo.key (.dynlibExternLib l)) α where
  family_key_eq_type := by unfold BuildData; simp

--------------------------------------------------------------------------------
/-! ## Build Info & Facets                                                    -/
--------------------------------------------------------------------------------

/-!
### Complex Builtin Facet Declarations

Additional builtin facets missing from `Build.Facets`.
These are defined here because they need configuration definitions
(e.g., `Module`), whereas the facets there are needed by the configuration
definitions.
-/

/-- The direct local imports of the Lean module. -/
abbrev Module.importsFacet := `imports
module_data imports : Array Module

/-- The transitive local imports of the Lean module. -/
abbrev Module.transImportsFacet := `transImports
module_data transImports : Array Module

/-- The transitive local imports of the Lean module. -/
abbrev Module.precompileImportsFacet := `precompileImports
module_data precompileImports : Array Module

/-- Shared library for `--load-dynlib`. -/
abbrev Module.dynlibFacet := `dynlib
module_data dynlib : Dynlib

/-- A Lean library's Lean modules. -/
abbrev LeanLib.modulesFacet := `modules
library_data modules : Array Module

/-- The package's array of dependencies. -/
abbrev Package.depsFacet := `deps
package_data deps : Array Package

/-- The package's complete array of transitive dependencies. -/
abbrev Package.transDepsFacet := `transDeps
package_data transDeps : Array Package

/-!
### Facet Build Info Helper Constructors

Definitions to easily construct `BuildInfo` values for module, package,
and target facets.
-/

namespace Module

/-- Build info for the module's specified facet. -/
abbrev facet (facet : Name) (self : Module) : BuildInfo :=
  .moduleFacet self facet

@[inherit_doc importsFacet] abbrev imports (self : Module) :=
  self.facet importsFacet

@[inherit_doc transImportsFacet] abbrev transImports (self : Module) :=
  self.facet transImportsFacet

@[inherit_doc precompileImportsFacet] abbrev precompileImports (self : Module) :=
  self.facet precompileImportsFacet

@[inherit_doc depsFacet] abbrev deps  (self : Module) :=
  self.facet depsFacet

@[inherit_doc leanArtsFacet] abbrev leanArts  (self : Module) :=
  self.facet leanArtsFacet

@[inherit_doc oleanFacet] abbrev olean (self : Module) :=
  self.facet oleanFacet

@[inherit_doc ileanFacet] abbrev ilean (self : Module)  :=
  self.facet ileanFacet

@[inherit_doc cFacet] abbrev c (self : Module) :=
  self.facet cFacet

@[inherit_doc cFacet] abbrev bc (self : Module) :=
  self.facet bcFacet

@[inherit_doc oFacet] abbrev o (self : Module) :=
  self.facet oFacet

@[inherit_doc oExportFacet] abbrev oExport (self : Module) :=
  self.facet oExportFacet

@[inherit_doc oNoExportFacet] abbrev oNoExport (self : Module) :=
  self.facet oNoExportFacet

@[inherit_doc coFacet] abbrev co (self : Module) :=
  self.facet coFacet

@[inherit_doc coExportFacet] abbrev coExport (self : Module) :=
  self.facet coExportFacet

@[inherit_doc coNoExportFacet] abbrev coNoExport (self : Module) :=
  self.facet coNoExportFacet

@[inherit_doc bcoFacet] abbrev bco (self : Module) :=
  self.facet bcoFacet

@[inherit_doc dynlibFacet] abbrev dynlib (self : Module) :=
  self.facet dynlibFacet

end Module

/-- Build info for the package's specified facet. -/
abbrev Package.facet (facet : Name) (self : Package) : BuildInfo :=
  .packageFacet self facet

@[inherit_doc buildCacheFacet]
abbrev Package.buildCache (self : Package) : BuildInfo :=
  self.facet buildCacheFacet

@[inherit_doc optBuildCacheFacet]
abbrev Package.optBuildCache (self : Package) : BuildInfo :=
  self.facet optBuildCacheFacet

@[inherit_doc reservoirBarrelFacet]
abbrev Package.reservoirBarrel (self : Package) : BuildInfo :=
  self.facet reservoirBarrelFacet

@[inherit_doc optReservoirBarrelFacet]
abbrev Package.optReservoirBarrel (self : Package) : BuildInfo :=
  self.facet optReservoirBarrelFacet

@[inherit_doc gitHubReleaseFacet]
abbrev Package.gitHubRelease (self : Package) : BuildInfo :=
  self.facet gitHubReleaseFacet

@[inherit_doc optGitHubReleaseFacet]
abbrev Package.optGitHubRelease (self : Package) : BuildInfo :=
  self.facet optGitHubReleaseFacet

@[deprecated gitHubRelease (since := "2024-09-27")]
abbrev Package.release := @gitHubRelease

@[deprecated optGitHubRelease (since := "2024-09-27")]
abbrev Package.optRelease := @optGitHubRelease

@[inherit_doc extraDepFacet]
abbrev Package.extraDep (self : Package) : BuildInfo :=
  self.facet extraDepFacet

@[inherit_doc depsFacet]
abbrev Package.deps (self : Package) : BuildInfo :=
  self.facet depsFacet

@[inherit_doc transDepsFacet]
abbrev Package.transDeps (self : Package) : BuildInfo :=
  self.facet transDepsFacet

/-- Build info for a custom package target. -/
abbrev Package.target (target : Name) (self : Package) : BuildInfo :=
  .target self target

/-- Build info of the Lean library's Lean binaries. -/
abbrev LeanLib.facet (self : LeanLib) (facet : Name) : BuildInfo :=
  .libraryFacet self facet

@[inherit_doc modulesFacet]
abbrev LeanLib.modules (self : LeanLib) : BuildInfo :=
  self.facet modulesFacet

@[inherit_doc leanArtsFacet]
abbrev LeanLib.leanArts (self : LeanLib) : BuildInfo :=
  self.facet leanArtsFacet

@[inherit_doc staticFacet]
abbrev LeanLib.static (self : LeanLib) : BuildInfo :=
  self.facet staticFacet

@[inherit_doc staticExportFacet]
abbrev LeanLib.staticExport (self : LeanLib) : BuildInfo :=
  self.facet staticExportFacet

@[inherit_doc sharedFacet]
abbrev LeanLib.shared (self : LeanLib) : BuildInfo :=
  self.facet sharedFacet

@[inherit_doc extraDepFacet]
abbrev LeanLib.extraDep (self : LeanLib) : BuildInfo :=
  self.facet extraDepFacet

/-- Build info of the Lean executable. -/
abbrev LeanExe.exe (self : LeanExe) : BuildInfo :=
  .leanExe self

/-- Build info of the external library's static binary. -/
abbrev ExternLib.static (self : ExternLib) : BuildInfo :=
  .staticExternLib self

/-- Build info of the external library's shared binary. -/
abbrev ExternLib.shared (self : ExternLib) : BuildInfo :=
  .sharedExternLib self

/-- Build info of the external library's dynlib. -/
abbrev ExternLib.dynlib (self : ExternLib) : BuildInfo :=
  .dynlibExternLib self
