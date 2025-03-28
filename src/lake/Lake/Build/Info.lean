/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.LeanExe
import Lake.Config.ExternLib
import Lake.Config.InputFile
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
| target (package : Package) (target : Name)
| facet (target : BuildKey) (kind : Name) (data : DataType.{0} kind) (facet : Name)

--------------------------------------------------------------------------------
/-! ## Build Info & Keys                                                      -/
--------------------------------------------------------------------------------

/-! ### Build Key Helper Constructors -/

abbrev Module.key (self : Module) : BuildKey :=
  .module self.keyName

@[deprecated Module.key (since := "2025-03-28")]
abbrev Module.buildKey (self : Module) : BuildKey :=
  .module self.keyName

@[deprecated BuildKey.facet (since := "2025-03-28")]
abbrev Module.facetBuildKey (facet : Name) (self : Module) : BuildKey :=
  self.key.facet facet

abbrev Package.key (self : Package) : BuildKey :=
  .package self.name

@[deprecated Package.key (since := "2025-03-28")]
abbrev Package.buildKey (self : Package) : BuildKey :=
  .package self.name

@[deprecated BuildKey.facet (since := "2025-03-28")]
abbrev Package.facetBuildKey (facet : Name) (self : Package) : BuildKey :=
  self.key.facet facet

abbrev Package.targetKey (target : Name) (self : Package) : BuildKey :=
  .packageTarget self.name target

@[deprecated Package.targetKey (since := "2025-03-28")]
abbrev Package.targetBuildKey (target : Name) (self : Package) : BuildKey :=
  .packageTarget self.name target

abbrev ConfigTarget.key (self : ConfigTarget kind) : BuildKey :=
  .packageTarget self.pkg.name self.name

@[deprecated ConfigTarget.key (since := "2025-03-28")]
abbrev ConfigTarget.buildKey (self : ConfigTarget kind) : BuildKey :=
  .packageTarget self.pkg.name self.name

@[deprecated BuildKey.facet (since := "2025-03-28")]
abbrev ConfigTarget.facetBuildKey (self : ConfigTarget kind) (facet : Name) : BuildKey :=
  self.key.facet facet

abbrev LeanExe.exeBuildKey (self : LeanExe) : BuildKey :=
  self.key.facet exeFacet

abbrev ExternLib.staticBuildKey (self : ExternLib) : BuildKey :=
  self.key.facet staticFacet

abbrev ExternLib.sharedBuildKey (self : ExternLib) : BuildKey :=
  self.key.facet sharedFacet

abbrev ExternLib.dynlibBuildKey (self : ExternLib) : BuildKey :=
  self.key.facet dynlibFacet

/-! ### Build Info to Key -/

/-- The key that identifies the build in the Lake build store. -/
@[reducible] def BuildInfo.key : (self : BuildInfo) → BuildKey
| target p t => p.targetKey t
| facet (target := t) (facet := f) .. => .facet t f

instance : ToString BuildInfo := ⟨(toString ·.key)⟩

/-! ### Instances for deducing data types of `BuildInfo` keys -/

instance (priority := low) {p : NPackage n} : FamilyDef BuildData
  (.customTarget p.toPackage.name t) (CustomData n t) := ⟨by simp⟩

instance {p : NPackage n} [FamilyOut (CustomData n) t α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t)) α where
  fam_eq := by unfold BuildData; simp

instance {p : NPackage n} [FamilyOut BuildData (.packageTarget n t) α]
: FamilyDef BuildData (BuildInfo.key (.target p.toPackage t)) α where
  fam_eq := by unfold BuildInfo.key Package.targetKey; simp

instance [FamilyOut FacetOut f α]
: FamilyDef BuildData (BuildInfo.key (.facet t k d f)) α where
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

data_type module : Module
data_type package : Package
data_type lean_lib : LeanLib
data_type lean_exe : LeanExe
data_type extern_lib : ExternLib
data_type input_file : InputFile
data_type input_dir : InputDir

/-- The direct local imports of the Lean module. -/
builtin_facet imports : Module => Array Module

/-- The transitive local imports of the Lean module. -/
builtin_facet transImports : Module => Array Module

/-- The transitive local imports of the Lean module. -/
builtin_facet precompileImports : Module => Array Module

/-- Shared library for `--load-dynlib`. -/
builtin_facet dynlib : Module => Dynlib

/-- A Lean library's Lean modules. -/
builtin_facet modules : LeanLib => Array Module

/-- The package's array of dependencies. -/
builtin_facet deps : Package => Array Package

/-- The package's complete array of transitive dependencies. -/
builtin_facet transDeps : Package => Array Package

/-!
### Facet Build Info Helper Constructors

Definitions to easily construct `BuildInfo` values for module, package,
and target facets.
-/

/-! #### Module Infos -/

/--
Build info for applying the specified facet to the module.
It is the user's obiligation to ensure the facet in question is a module facet.
-/
abbrev Module.facetCore (facet : Name) (self : Module) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info for a module facet. -/
abbrev Module.facet (facet : Name) (self : Module) : BuildInfo :=
  self.facetCore (Module.facetKind ++ facet)

@[deprecated Module.facetCore (since := "2025-03-04")]
abbrev BuildInfo.moduleFacet (module : Module) (facet : Name) : BuildInfo :=
  module.facetCore facet

namespace Module

@[inherit_doc importsFacet] abbrev imports (self : Module) :=
  self.facetCore importsFacet

@[inherit_doc transImportsFacet] abbrev transImports (self : Module) :=
  self.facetCore transImportsFacet

@[inherit_doc precompileImportsFacet] abbrev precompileImports (self : Module) :=
  self.facetCore precompileImportsFacet

@[inherit_doc depsFacet] abbrev deps  (self : Module) :=
  self.facetCore depsFacet

@[inherit_doc leanArtsFacet] abbrev leanArts  (self : Module) :=
  self.facetCore leanArtsFacet

@[inherit_doc oleanFacet] abbrev olean (self : Module) :=
  self.facetCore oleanFacet

@[inherit_doc ileanFacet] abbrev ilean (self : Module)  :=
  self.facetCore ileanFacet

@[inherit_doc cFacet] abbrev c (self : Module) :=
  self.facetCore cFacet

@[inherit_doc cFacet] abbrev bc (self : Module) :=
  self.facetCore bcFacet

@[inherit_doc oFacet] abbrev o (self : Module) :=
  self.facetCore oFacet

@[inherit_doc oExportFacet] abbrev oExport (self : Module) :=
  self.facetCore oExportFacet

@[inherit_doc oNoExportFacet] abbrev oNoExport (self : Module) :=
  self.facetCore oNoExportFacet

@[inherit_doc coFacet] abbrev co (self : Module) :=
  self.facetCore coFacet

@[inherit_doc coExportFacet] abbrev coExport (self : Module) :=
  self.facetCore coExportFacet

@[inherit_doc coNoExportFacet] abbrev coNoExport (self : Module) :=
  self.facetCore coNoExportFacet

@[inherit_doc bcoFacet] abbrev bco (self : Module) :=
  self.facetCore bcoFacet

@[inherit_doc dynlibFacet] abbrev dynlib (self : Module) :=
  self.facetCore dynlibFacet

end Module

/-! #### Package Infos -/

/-- Build info for a package target (e.g., a library, executable, or custom target). -/
abbrev Package.target (target : Name) (self : Package) : BuildInfo :=
  .target self target

/-
Build info for applying the specified facet to the package.
It is the user's obiligation to ensure the facet in question is a package facet.
-/
abbrev Package.facetCore (facet : Name) (self : Package) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info for a package facet. -/
abbrev Package.facet (facet : Name) (self : Package) : BuildInfo :=
  self.facetCore (Package.facetKind ++ facet)

@[deprecated Package.facetCore (since := "2025-03-04")]
abbrev BuildInfo.packageFacet (package : Package) (facet : Name) : BuildInfo :=
  package.facetCore facet

namespace Package

@[inherit_doc buildCacheFacet]
abbrev buildCache (self : Package) : BuildInfo :=
  self.facetCore buildCacheFacet

@[inherit_doc optBuildCacheFacet]
abbrev optBuildCache (self : Package) : BuildInfo :=
  self.facetCore optBuildCacheFacet

@[inherit_doc reservoirBarrelFacet]
abbrev reservoirBarrel (self : Package) : BuildInfo :=
  self.facetCore reservoirBarrelFacet

@[inherit_doc optReservoirBarrelFacet]
abbrev optReservoirBarrel (self : Package) : BuildInfo :=
  self.facetCore optReservoirBarrelFacet

@[inherit_doc gitHubReleaseFacet]
abbrev gitHubRelease (self : Package) : BuildInfo :=
  self.facetCore gitHubReleaseFacet

@[inherit_doc optGitHubReleaseFacet]
abbrev optGitHubRelease (self : Package) : BuildInfo :=
  self.facetCore optGitHubReleaseFacet

@[deprecated gitHubRelease (since := "2024-09-27")]
abbrev release := @gitHubRelease

@[deprecated optGitHubRelease (since := "2024-09-27")]
abbrev optRelease := @optGitHubRelease

@[inherit_doc extraDepFacet]
abbrev extraDep (self : Package) : BuildInfo :=
  self.facetCore extraDepFacet

@[inherit_doc depsFacet]
abbrev deps (self : Package) : BuildInfo :=
  self.facetCore depsFacet

@[inherit_doc transDepsFacet]
abbrev transDeps (self : Package) : BuildInfo :=
  self.facetCore transDepsFacet

end Package

/-! #### Lean Library Infos -/

/-
Build info for applying the specified facet to the library.
It is the user's obiligation to ensure the facet in question is a library facet.
-/
abbrev LeanLib.facetCore (facet : Name) (self : LeanLib) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info for a facet of a Lean library. -/
abbrev LeanLib.facet (facet : Name) (self : LeanLib) : BuildInfo :=
  self.facetCore (LeanLib.facetKind ++ facet)

@[deprecated LeanLib.facetCore (since := "2025-03-04")]
abbrev BuildInfo.libraryFacet (lib : LeanLib) (facet : Name) : BuildInfo :=
  lib.facetCore facet

namespace LeanLib

@[inherit_doc modulesFacet]
abbrev modules (self : LeanLib) : BuildInfo :=
  self.facetCore modulesFacet

@[inherit_doc leanArtsFacet]
abbrev leanArts (self : LeanLib) : BuildInfo :=
  self.facetCore leanArtsFacet

@[inherit_doc staticFacet]
abbrev static (self : LeanLib) : BuildInfo :=
  self.facetCore staticFacet

@[inherit_doc staticExportFacet]
abbrev staticExport (self : LeanLib) : BuildInfo :=
  self.facetCore staticExportFacet

@[inherit_doc sharedFacet]
abbrev shared (self : LeanLib) : BuildInfo :=
  self.facetCore sharedFacet

@[inherit_doc extraDepFacet]
abbrev extraDep (self : LeanLib) : BuildInfo :=
  self.facetCore extraDepFacet

end LeanLib

/-! #### Lean Executable Infos -/

/-
Build info for applying the specified facet to the executable.
It is the user's obiligation to ensure the facet in question is the executable facet.
-/
abbrev LeanExe.facetCore (facet : Name) (self : LeanExe) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the Lean executable. -/
abbrev LeanExe.exe (self : LeanExe) : BuildInfo :=
  self.facetCore LeanExe.exeFacet

@[deprecated LeanExe.exe (since := "2025-03-04")]
abbrev BuildInfo.leanExe (exe : LeanExe) : BuildInfo :=
  exe.exe

/-! #### External Library Infos -/

/-
Build info for applying the specified facet to the external library.
It is the user's obiligation to ensure the facet in question is an external library facet.
-/
abbrev ExternLib.facetCore (facet : Name) (self : ExternLib) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the external library's static binary. -/
abbrev ExternLib.static (self : ExternLib) : BuildInfo :=
  self.facetCore ExternLib.staticFacet

@[deprecated ExternLib.static (since := "2025-03-04")]
abbrev BuildInfo.staticExternLib (lib : ExternLib) : BuildInfo :=
  lib.facetCore ExternLib.staticFacet

/-- Build info of the external library's shared binary. -/
abbrev ExternLib.shared (self : ExternLib) : BuildInfo :=
  self.facetCore ExternLib.sharedFacet

@[deprecated ExternLib.shared (since := "2025-03-04")]
abbrev BuildInfo.sharedExternLib (lib : ExternLib) : BuildInfo :=
  lib.facetCore  ExternLib.sharedFacet

/-- Build info of the external library's dynlib. -/
abbrev ExternLib.dynlib (self : ExternLib) : BuildInfo :=
  self.facetCore ExternLib.dynlibFacet

@[deprecated ExternLib.dynlib (since := "2025-03-04")]
abbrev BuildInfo.dynlibExternLib (lib : ExternLib) : BuildInfo :=
  lib.facetCore ExternLib.dynlibFacet

/-! #### Input File & Directory Infos -/

/-
Build info for applying the specified facet to the input file.
It is the user's obiligation to ensure the facet in question is an external library facet.
-/
abbrev InputFile.facetCore (facet : Name) (self : InputFile) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the input file's default facet. -/
abbrev InputFile.default (self : InputFile) : BuildInfo :=
  self.facetCore InputFile.defaultFacet

/-
Build info for applying the specified facet to the input directory.
It is the user's obiligation to ensure the facet in question is an external library facet.
-/
abbrev InputDir.facetCore (facet : Name) (self : InputDir) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the input directory's default facet. -/
abbrev InputDir.default (self : InputDir) : BuildInfo :=
  self.facetCore InputDir.defaultFacet
