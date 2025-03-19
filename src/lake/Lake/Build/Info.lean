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
| target (package : Package) (target : Name) (kind := Name.anonymous)
| facet (target : BuildKey) (data : TargetData target.kind) (facet : Name)

--------------------------------------------------------------------------------
/-! ## Build Info & Keys                                                      -/
--------------------------------------------------------------------------------

/-! ### Build Key Helper Constructors -/

abbrev Module.buildKey (self : Module) : BuildKey :=
  .module self.keyName

abbrev Module.facetBuildKey (facet : Name) (self : Module) : BuildKey :=
  .moduleFacet self.keyName facet

abbrev Package.buildKey (self : Package) : BuildKey :=
  .package self.name

abbrev Package.facetBuildKey (facet : Name) (self : Package) : BuildKey :=
  .packageFacet self.name facet

abbrev Package.targetBuildKey
  (target : Name) (self : Package) (kind := Name.anonymous)
: BuildKey := .packageTarget self.name target kind

abbrev LeanLib.buildKey (self : LeanLib) : BuildKey :=
  .packageTarget self.pkg.name self.name facetKind

abbrev LeanLib.facetBuildKey (self : LeanLib) (facet : Name) : BuildKey :=
  .targetFacet self.pkg.name self.name facetKind facet

abbrev LeanExe.buildKey (self : LeanExe) : BuildKey :=
  .packageTarget self.pkg.name self.name facetKind

abbrev LeanExe.exeBuildKey (self : LeanExe) : BuildKey :=
  .targetFacet self.pkg.name self.name facetKind exeFacet

abbrev ExternLib.buildKey (self : ExternLib) : BuildKey :=
  .packageTarget self.pkg.name self.name facetKind

abbrev ExternLib.facetBuildKey (facet : Name) (self : ExternLib) : BuildKey :=
  .targetFacet self.pkg.name self.name facetKind facet

abbrev ExternLib.staticBuildKey (self : ExternLib) : BuildKey :=
  self.facetBuildKey staticFacet

abbrev ExternLib.sharedBuildKey (self : ExternLib) : BuildKey :=
  self.facetBuildKey sharedFacet

abbrev ExternLib.dynlibBuildKey (self : ExternLib) : BuildKey :=
  self.facetBuildKey dynlibFacet

/-! ### Build Info to Key -/

/-- The key that identifies the build in the Lake build store. -/
@[reducible] def BuildInfo.key : (self : BuildInfo) → BuildKey
| target p t k => p.targetBuildKey t k
| facet t _ f => .facet t f

instance : ToString BuildInfo := ⟨(toString ·.key)⟩

/-! ### Instances for deducing data types of `BuildInfo` keys -/

instance [FamilyOut ModuleData f α]
: FamilyDef BuildData (BuildInfo.key (.facet (.module m) d f)) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut PackageData f α]
: FamilyDef BuildData (BuildInfo.key (.facet (.package p) d f)) α where
  fam_eq := by unfold BuildData; simp

instance (priority := low) {p : NPackage n} : FamilyDef BuildData
  (.customTarget p.toPackage.name t) (CustomData n t) := ⟨by simp⟩

instance {p : NPackage n} [FamilyOut (CustomData n) t α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t)) α where
  fam_eq := by unfold BuildData; simp

instance {p : NPackage n} [FamilyOut BuildData (.packageTarget n t k) α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t k)) α where
  fam_eq := by unfold BuildInfo.key Package.targetBuildKey; simp

instance [FamilyOut (FacetData k) f α]
: FamilyDef BuildData (BuildInfo.key (.facet (.packageTarget p t k) d f)) α where
  fam_eq := by unfold BuildData; simp

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

target_data module : Module
target_data package : Package
target_data leanLib : LeanLib
target_data leanExe : LeanExe
target_data externLib : ExternLib

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

/-- Build info for the module's specified facet. -/
abbrev Module.facet (facet : Name) (self : Module) : BuildInfo :=
  .facet self.buildKey (toFamily self) facet

@[deprecated Module.facet (since := "2025-03-04")]
abbrev BuildInfo.moduleFacet (module : Module) (facet : Name) : BuildInfo :=
  module.facet facet

namespace Module

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

/-- Build info for a package target (e.g., a library, executable, or custom target). -/
abbrev Package.target (target : Name) (self : Package) (kind := Name.anonymous) : BuildInfo :=
  .target self target kind

/-- Build info for the package's specified facet. -/
abbrev Package.facet (facet : Name) (self : Package) : BuildInfo :=
  .facet self.buildKey (toFamily self) facet

@[deprecated Package.facet (since := "2025-03-04")]
abbrev BuildInfo.packageFacet (package : Package) (facet : Name) : BuildInfo :=
  package.facet facet

namespace Package

@[inherit_doc buildCacheFacet]
abbrev buildCache (self : Package) : BuildInfo :=
  self.facet buildCacheFacet

@[inherit_doc optBuildCacheFacet]
abbrev optBuildCache (self : Package) : BuildInfo :=
  self.facet optBuildCacheFacet

@[inherit_doc reservoirBarrelFacet]
abbrev reservoirBarrel (self : Package) : BuildInfo :=
  self.facet reservoirBarrelFacet

@[inherit_doc optReservoirBarrelFacet]
abbrev optReservoirBarrel (self : Package) : BuildInfo :=
  self.facet optReservoirBarrelFacet

@[inherit_doc gitHubReleaseFacet]
abbrev gitHubRelease (self : Package) : BuildInfo :=
  self.facet gitHubReleaseFacet

@[inherit_doc optGitHubReleaseFacet]
abbrev optGitHubRelease (self : Package) : BuildInfo :=
  self.facet optGitHubReleaseFacet

@[deprecated gitHubRelease (since := "2024-09-27")]
abbrev release := @gitHubRelease

@[deprecated optGitHubRelease (since := "2024-09-27")]
abbrev optRelease := @optGitHubRelease

@[inherit_doc extraDepFacet]
abbrev extraDep (self : Package) : BuildInfo :=
  self.facet extraDepFacet

@[inherit_doc depsFacet]
abbrev deps (self : Package) : BuildInfo :=
  self.facet depsFacet

@[inherit_doc transDepsFacet]
abbrev transDeps (self : Package) : BuildInfo :=
  self.facet transDepsFacet

end Package

/-- Build info for a facet of a Lean library. -/
abbrev LeanLib.facet (facet : Name) (self : LeanLib) : BuildInfo :=
  .facet self.buildKey (toFamily self) facet

@[deprecated LeanLib.facet (since := "2025-03-04")]
abbrev BuildInfo.libraryFacet (lib : LeanLib) (facet : Name) : BuildInfo :=
  lib.facet facet

namespace LeanLib

@[inherit_doc modulesFacet]
abbrev modules (self : LeanLib) : BuildInfo :=
  self.facet modulesFacet

@[inherit_doc leanArtsFacet]
abbrev leanArts (self : LeanLib) : BuildInfo :=
  self.facet leanArtsFacet

@[inherit_doc staticFacet]
abbrev static (self : LeanLib) : BuildInfo :=
  self.facet staticFacet

@[inherit_doc staticExportFacet]
abbrev staticExport (self : LeanLib) : BuildInfo :=
  self.facet staticExportFacet

@[inherit_doc sharedFacet]
abbrev shared (self : LeanLib) : BuildInfo :=
  self.facet sharedFacet

@[inherit_doc extraDepFacet]
abbrev extraDep (self : LeanLib) : BuildInfo :=
  self.facet extraDepFacet

end LeanLib

/--  Build info for a facet of a Lean executable. -/
abbrev LeanExe.facet (facet : Name) (self : LeanExe) : BuildInfo :=
  .facet self.buildKey (toFamily self) facet

/-- Build info of the Lean executable. -/
abbrev LeanExe.exe (self : LeanExe) : BuildInfo :=
  self.facet LeanExe.exeFacet

@[deprecated LeanExe.exe (since := "2025-03-04")]
abbrev BuildInfo.leanExe (exe : LeanExe) : BuildInfo :=
  exe.exe

/--  Build info for a facet of an external library. -/
abbrev ExternLib.facet (facet : Name) (self : ExternLib) : BuildInfo :=
  .facet self.buildKey (toFamily self) facet

/-- Build info of the external library's static binary. -/
abbrev ExternLib.static (self : ExternLib) : BuildInfo :=
  self.facet ExternLib.staticFacet

@[deprecated ExternLib.static (since := "2025-03-04")]
abbrev BuildInfo.staticExternLib (lib : ExternLib) : BuildInfo :=
  lib.facet ExternLib.staticFacet

/-- Build info of the external library's shared binary. -/
abbrev ExternLib.shared (self : ExternLib) : BuildInfo :=
  self.facet ExternLib.sharedFacet

@[deprecated ExternLib.shared (since := "2025-03-04")]
abbrev BuildInfo.sharedExternLib (lib : ExternLib) : BuildInfo :=
  lib.facet  ExternLib.sharedFacet

/-- Build info of the external library's dynlib. -/
abbrev ExternLib.dynlib (self : ExternLib) : BuildInfo :=
  self.facet ExternLib.dynlibFacet

@[deprecated ExternLib.dynlib (since := "2025-03-04")]
abbrev BuildInfo.dynlibExternLib (lib : ExternLib) : BuildInfo :=
  lib.facet ExternLib.dynlibFacet
