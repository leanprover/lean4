/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Info
public import Lake.Config.LeanExe
public import Lake.Config.ExternLib
public import Lake.Config.InputFile
meta import all Lake.Build.Data

/-!
# Build Keys, Infos, & Facets

This module defines the shorthand definitions for build keys, infos, and facets
on the various target types.
-/

open System Lean

namespace Lake

/-! ### Build Key Helper Constructors -/

public abbrev Module.key (self : Module) : BuildKey :=
  .packageModule self.pkg.keyName self.name

public abbrev ConfigTarget.key (self : ConfigTarget kind) : BuildKey :=
  .packageTarget self.pkg.keyName self.name

public abbrev LeanExe.exeBuildKey (self : LeanExe) : BuildKey :=
  self.key.facet exeFacet

public abbrev ExternLib.staticBuildKey (self : ExternLib) : BuildKey :=
  self.key.facet staticFacet

public abbrev ExternLib.sharedBuildKey (self : ExternLib) : BuildKey :=
  self.key.facet sharedFacet

public abbrev ExternLib.dynlibBuildKey (self : ExternLib) : BuildKey :=
  self.key.facet dynlibFacet

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

/-- An import statement with its resolved module within the workspace. -/
public structure ModuleImport extends Import where
  module? : Option Module

/-- A module's source file path plus its parsed header. -/
public structure ModuleInput where
  path : FilePath
  trace : BuildTrace
  header : ModuleHeader
  imports : Array ModuleImport

/--
The module's processed Lean source file.
Combines tracing the file with parsing its header.
-/
builtin_facet input : Module => ModuleInput

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
It is the user's obligation to ensure the facet in question is a module facet.
-/
public abbrev Module.facetCore (facet : Name) (self : Module) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info for a module facet. -/
public abbrev Module.facet (facet : Name) (self : Module) : BuildInfo :=
  self.facetCore (Module.facetKind ++ facet)

namespace Module

@[inherit_doc inputFacet] public abbrev input (self : Module) :=
  self.facetCore inputFacet

@[inherit_doc leanFacet] public abbrev lean (self : Module) :=
  self.facetCore leanFacet

@[inherit_doc headerFacet] public abbrev header (self : Module) :=
  self.facetCore headerFacet

@[inherit_doc importsFacet] public abbrev imports (self : Module) :=
  self.facetCore importsFacet

@[inherit_doc transImportsFacet] public abbrev transImports (self : Module) :=
  self.facetCore transImportsFacet

@[inherit_doc precompileImportsFacet] public abbrev precompileImports (self : Module) :=
  self.facetCore precompileImportsFacet

@[inherit_doc setupFacet] public abbrev setup  (self : Module) :=
  self.facetCore setupFacet

@[inherit_doc depsFacet] public abbrev deps  (self : Module) :=
  self.facetCore depsFacet

@[inherit_doc importInfoFacet] public abbrev importInfo (self : Module) :=
  self.facetCore importInfoFacet

@[inherit_doc exportInfoFacet] public abbrev exportInfo (self : Module) :=
  self.facetCore exportInfoFacet

@[inherit_doc importArtsFacet] public abbrev importArts (self : Module) :=
  self.facetCore importArtsFacet

@[inherit_doc importAllArtsFacet] public abbrev importAllArts (self : Module) :=
  self.facetCore importAllArtsFacet

@[inherit_doc leanArtsFacet] public abbrev leanArts (self : Module) :=
  self.facetCore leanArtsFacet

@[inherit_doc oleanFacet] public abbrev olean (self : Module) :=
  self.facetCore oleanFacet

@[inherit_doc oleanServerFacet] public abbrev oleanServer (self : Module) :=
  self.facetCore oleanServerFacet

@[inherit_doc oleanPrivateFacet] public abbrev oleanPrivate (self : Module) :=
  self.facetCore oleanPrivateFacet

@[inherit_doc ileanFacet] public abbrev ilean (self : Module)  :=
  self.facetCore ileanFacet

@[inherit_doc irFacet] public abbrev ir (self : Module) :=
  self.facetCore irFacet

@[inherit_doc cFacet] public abbrev c (self : Module) :=
  self.facetCore cFacet

@[inherit_doc cFacet] public abbrev bc (self : Module) :=
  self.facetCore bcFacet

@[inherit_doc oFacet] public abbrev o (self : Module) :=
  self.facetCore oFacet

@[inherit_doc oExportFacet] public abbrev oExport (self : Module) :=
  self.facetCore oExportFacet

@[inherit_doc oNoExportFacet] public abbrev oNoExport (self : Module) :=
  self.facetCore oNoExportFacet

@[inherit_doc coFacet] public abbrev co (self : Module) :=
  self.facetCore coFacet

@[inherit_doc coExportFacet] public abbrev coExport (self : Module) :=
  self.facetCore coExportFacet

@[inherit_doc coNoExportFacet] public abbrev coNoExport (self : Module) :=
  self.facetCore coNoExportFacet

@[inherit_doc bcoFacet] public abbrev bco (self : Module) :=
  self.facetCore bcoFacet

@[inherit_doc dynlibFacet] public abbrev dynlib (self : Module) :=
  self.facetCore dynlibFacet

end Module

/-! #### Package Infos -/

/-- Build info for a package target (e.g., a library, executable, or custom target). -/
public abbrev Package.target (target : Name) (self : Package) : BuildInfo :=
  .target self target

/-
Build info for applying the specified facet to the package.
It is the user's obligation to ensure the facet in question is a package facet.
-/
public abbrev Package.facetCore (facet : Name) (self : Package) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info for a package facet. -/
public abbrev Package.facet (facet : Name) (self : Package) : BuildInfo :=
  self.facetCore (Package.facetKind ++ facet)

namespace Package

@[inherit_doc buildCacheFacet]
public abbrev buildCache (self : Package) : BuildInfo :=
  self.facetCore buildCacheFacet

@[inherit_doc optBuildCacheFacet]
public abbrev optBuildCache (self : Package) : BuildInfo :=
  self.facetCore optBuildCacheFacet

@[inherit_doc reservoirBarrelFacet]
public abbrev reservoirBarrel (self : Package) : BuildInfo :=
  self.facetCore reservoirBarrelFacet

@[inherit_doc optReservoirBarrelFacet]
public abbrev optReservoirBarrel (self : Package) : BuildInfo :=
  self.facetCore optReservoirBarrelFacet

@[inherit_doc gitHubReleaseFacet]
public abbrev gitHubRelease (self : Package) : BuildInfo :=
  self.facetCore gitHubReleaseFacet

@[inherit_doc optGitHubReleaseFacet]
public abbrev optGitHubRelease (self : Package) : BuildInfo :=
  self.facetCore optGitHubReleaseFacet

@[inherit_doc extraDepFacet]
public abbrev extraDep (self : Package) : BuildInfo :=
  self.facetCore extraDepFacet

@[inherit_doc depsFacet]
public abbrev deps (self : Package) : BuildInfo :=
  self.facetCore depsFacet

@[inherit_doc transDepsFacet]
public abbrev transDeps (self : Package) : BuildInfo :=
  self.facetCore transDepsFacet

end Package

/-! #### Lean Library Infos -/

/-
Build info for applying the specified facet to the library.
It is the user's obligation to ensure the facet in question is a library facet.
-/
public abbrev LeanLib.facetCore (facet : Name) (self : LeanLib) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info for a facet of a Lean library. -/
public abbrev LeanLib.facet (facet : Name) (self : LeanLib) : BuildInfo :=
  self.facetCore (LeanLib.facetKind ++ facet)

namespace LeanLib

@[inherit_doc modulesFacet]
public abbrev modules (self : LeanLib) : BuildInfo :=
  self.facetCore modulesFacet

@[inherit_doc leanArtsFacet]
public abbrev leanArts (self : LeanLib) : BuildInfo :=
  self.facetCore leanArtsFacet

@[inherit_doc staticFacet]
public abbrev static (self : LeanLib) : BuildInfo :=
  self.facetCore staticFacet

@[inherit_doc staticExportFacet]
public abbrev staticExport (self : LeanLib) : BuildInfo :=
  self.facetCore staticExportFacet

@[inherit_doc sharedFacet]
public abbrev shared (self : LeanLib) : BuildInfo :=
  self.facetCore sharedFacet

@[inherit_doc extraDepFacet]
public abbrev extraDep (self : LeanLib) : BuildInfo :=
  self.facetCore extraDepFacet

end LeanLib

/-! #### Lean Executable Infos -/

/-
Build info for applying the specified facet to the executable.
It is the user's obligation to ensure the facet in question is the executable facet.
-/
public abbrev LeanExe.facetCore (facet : Name) (self : LeanExe) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the Lean executable. -/
public abbrev LeanExe.exe (self : LeanExe) : BuildInfo :=
  self.facetCore LeanExe.exeFacet

/-! #### External Library Infos -/

/-
Build info for applying the specified facet to the external library.
It is the user's obligation to ensure the facet in question is an external library facet.
-/
public abbrev ExternLib.facetCore (facet : Name) (self : ExternLib) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the external library's static binary. -/
public abbrev ExternLib.static (self : ExternLib) : BuildInfo :=
  self.facetCore ExternLib.staticFacet

/-- Build info of the external library's shared binary. -/
public abbrev ExternLib.shared (self : ExternLib) : BuildInfo :=
  self.facetCore ExternLib.sharedFacet

/-- Build info of the external library's dynlib. -/
public abbrev ExternLib.dynlib (self : ExternLib) : BuildInfo :=
  self.facetCore ExternLib.dynlibFacet

/-! #### Input File & Directory Infos -/

/-
Build info for applying the specified facet to the input file.
It is the user's obligation to ensure the facet in question is an external library facet.
-/
public abbrev InputFile.facetCore (facet : Name) (self : InputFile) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the input file's default facet. -/
public abbrev InputFile.default (self : InputFile) : BuildInfo :=
  self.facetCore InputFile.defaultFacet

/-
Build info for applying the specified facet to the input directory.
It is the user's obligation to ensure the facet in question is an external library facet.
-/
public abbrev InputDir.facetCore (facet : Name) (self : InputDir) : BuildInfo :=
  .facet self.key facetKind (toFamily self) facet

/-- Build info of the input directory's default facet. -/
public abbrev InputDir.default (self : InputDir) : BuildInfo :=
  self.facetCore InputDir.defaultFacet
