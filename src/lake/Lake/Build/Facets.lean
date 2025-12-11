/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Job.Basic
public import Lake.Build.ModuleArtifacts
meta import all Lake.Build.Data

/-!
# Simple Builtin Facet Declarations

This module contains the definitions of most of the builtin facets.
The others are defined `Build.Info`. The facets there require configuration
definitions (e.g., `Module`), and some of the facets here are used in said
definitions.
-/

open System
open Lean hiding SearchPath

namespace Lake

/-! ## Module Facets -/

/-- A module facet name along with proof of its data type. -/
public structure ModuleFacet (α) where
  /-- The name of the module facet. -/
  name : Name
  /-- Proof that module's facet build result is of type α. -/
  data_eq : FacetOut name = α
  deriving Repr

public instance (facet : ModuleFacet α) : FamilyDef FacetOut facet.name α :=
  ⟨facet.data_eq⟩

public instance [FamilyOut FacetOut facet α] : CoeDep Name facet (ModuleFacet α) :=
  ⟨facet, FamilyOut.fam_eq⟩

/-- The module's Lean source file. -/
builtin_facet lean : Module => FilePath

/-- The parsed module header of the module's source file. -/
builtin_facet header : Module => ModuleHeader

/--
The computed configuration of a module for Lean.

In the process, this facet will build all of a module's dependencies,
including transitive imports, plugins, and those specified by `needs`.
-/
builtin_facet setup : Module => ModuleSetup

/--
This facet builds all of a module's dependencies,
including transitive imports, plugins, and those specified by `needs`.
-/
builtin_facet deps : Module => Opaque

/-- Information about the imports of a module. -/
public structure ModuleImportInfo where
  /-- Artifacts directly needed for the imports of the module. -/
  directArts : NameMap ImportArtifacts
  /-- The trace produced by mixing the traces of `directArts` with their transitive imports. -/
  trace : BuildTrace
  /-- Transitive import trace for an `import` of the module with the module system enabled. -/
  transTrace : BuildTrace
  /-- Transitive import trace for a `meta import` of the module. -/
  metaTransTrace : BuildTrace
  /-- Transitive import trace for an `import all` of the module. -/
  allTransTrace : BuildTrace
  /-- Transitive import trace for an `import` of the module without the module system enabled. -/
  legacyTransTrace : BuildTrace
  deriving Inhabited

/-- **For internal use only.** Information about the imports of this module. -/
builtin_facet importInfo : Module => ModuleImportInfo

/-- Information useful to importers of a module. -/
public structure ModuleExportInfo where
  /-- The trace of the module's source file. -/
  srcTrace : BuildTrace
  /-- Artifacts directly needed for an `import` of the module with the module system enabled. -/
  arts : ImportArtifacts
  /-- The trace of the module's public olean. -/
  artsTrace : BuildTrace
  /-- The trace of the module's public olean and IR. -/
  metaArtsTrace : BuildTrace
  /--
  Artifacts directly needed for an `import` of the module from a module without the module
  system enabled or `import all` of the module from a module with it enabled.
  -/
  allArts : ImportArtifacts
  /-- The trace produced by mixing the traces of `allArts`. -/
  allArtsTrace : BuildTrace
  /-- Transitive import trace for an `import` of the module with the module system enabled. -/
  transTrace : BuildTrace
  /-- Transitive import trace for a `meta import` of the module. -/
  metaTransTrace : BuildTrace
  /-- Transitive import trace for an `import all` of the module. -/
  allTransTrace : BuildTrace
  /-- Transitive import trace for an `import` of the module without the module system enabled. -/
  legacyTransTrace : BuildTrace
  deriving Inhabited

/-- **For internal use only.** Information useful to importers of this module. -/
builtin_facet exportInfo : Module => ModuleExportInfo

/-- Artifacts directly needed for an `import` of this module with the module system enabled. -/
builtin_facet importArts : Module => ImportArtifacts

/--
Artifacts directly needed for an `import` of this module from a module without the module
system enabled or `import all` of this module from a module with it enabled.
-/
builtin_facet importAllArts : Module => ImportArtifacts

/--
The core build facet of a Lean file.
Elaborates the Lean file via `lean` and produces all the Lean artifacts
of the module (e.g., `olean`, `ilean`, `c`).
Its trace just includes its dependencies.
-/
builtin_facet leanArts : Module => ModuleOutputArtifacts

/-- The `olean` file produced by `lean`. -/
builtin_facet olean : Module => FilePath

/-- The `olean.server` file produced by `lean` (with the module system enabled). -/
builtin_facet oleanServerFacet @ olean.server : Module => FilePath

/-- The `olean.private` file produced by `lean` (with the module system enabled). -/
builtin_facet oleanPrivateFacet @ olean.private : Module => FilePath

/-- The `ilean` file produced by `lean`. -/
builtin_facet ilean : Module => FilePath

/-- The `ir` file produced by `lean` (with the module system enabled). -/
builtin_facet ir : Module => FilePath

/-- The C file produced by `lean`. -/
builtin_facet c : Module => FilePath

/-- The LLVM bitcode (`bc`) file produced by `lean`. -/
builtin_facet bc : Module => FilePath

/--
The object file `.c.o` built from `c`.
On Windows, this is `c.o.noexport`, on other systems it is `c.o.export`).
-/
builtin_facet coFacet @ c.o : Module => FilePath

/-- The object file `.c.o.export` built from `c` (with `-DLEAN_EXPORTING`). -/
builtin_facet coExportFacet @ c.o.export : Module => FilePath

/-- The object file `.c.o.noexport` built from `c` (without `-DLEAN_EXPORTING`). -/
builtin_facet coNoExportFacet @ c.o.noexport : Module => FilePath

/-- The object file `.bc.o` built from `bc`. -/
builtin_facet bcoFacet @ bc.o : Module => FilePath

/--
The object file built from `c`/`bc`.
On Windows with the C backend, no Lean symbols are exported.
On every other configuration, symbols are exported.
-/
builtin_facet o : Module => FilePath

/-- The object file built from `c`/`bc` (with Lean symbols exported). -/
builtin_facet oExportFacet @ o.export : Module => FilePath

/-- The object file built from `c`/`bc` (without Lean symbols exported). -/
builtin_facet oNoExportFacet @ o.noexport : Module => FilePath


/-! ## Package Facets -/

/--
A package's *optional* cached build archive (e.g., from Reservoir or GitHub).
Will NOT cause the whole build to fail if the archive cannot be fetched.
-/
builtin_facet optBuildCacheFacet @ optCache : Package => Bool

/--
A package's cached build archive (e.g., from Reservoir or GitHub).
Will cause the whole build to fail if the archive cannot be fetched.
-/
builtin_facet buildCacheFacet @ cache : Package => Unit

/--
A package's *optional* build archive from Reservoir.
Will NOT cause the whole build to fail if the barrel cannot be fetched.
-/
builtin_facet optReservoirBarrelFacet @ optBarrel : Package => Bool

/--
A package's Reservoir build archive from Reservoir.
Will cause the whole build to fail if the barrel cannot be fetched.
-/
builtin_facet reservoirBarrelFacet @ barrel : Package => Unit

/--
A package's *optional* build archive from a GitHub release.
Will NOT cause the whole build to fail if the release cannot be fetched.
-/
builtin_facet optGitHubReleaseFacet @ optRelease : Package => Bool

/--
A package's build archive from a GitHub release.
Will cause the whole build to fail if the release cannot be fetched.
-/
builtin_facet gitHubReleaseFacet @ release : Package => Unit

/-- A package's `extraDepTargets` mixed with its transitive dependencies'. -/
builtin_facet extraDep : Package => Unit

/-! ## Target Facets -/

/-- The library's default facets (as specified by its `defaultFacets` configuration). . -/
builtin_facet default : LeanLib => Unit

/-- A Lean library's Lean artifacts (e.g., `olean`, `ilean`, `c`). -/
builtin_facet leanArts : LeanLib => Unit

/-- A Lean library's static artifact. -/
builtin_facet static : LeanLib => FilePath

/--
A Lean library's static artifact (with exported symbols).

Static libraries with explicit exports are built as thin libraries.
Such libraries are usually used as part of the local build process of some
shared artifact and not publicly distributed. Standard static libraries are
much better for distribution.
-/
builtin_facet staticExportFacet @ static.export : LeanLib => FilePath

/-- A Lean library's shared artifact. -/
builtin_facet shared : LeanLib => Dynlib

/-- A Lean library's `extraDepTargets` mixed with its package's. -/
builtin_facet extraDep : LeanLib => Unit

/-- The executable's default facet (i.e., an alias for `exe`) -/
builtin_facet default : LeanExe => FilePath

/-- A Lean binary executable. -/
builtin_facet exe : LeanExe => FilePath

/-- The external library's default facet (i.e., an alias for `static`) -/
builtin_facet default : ExternLib => FilePath

/-- A external library's static binary. -/
builtin_facet static : ExternLib => FilePath

/-- A external library's shared binary. -/
builtin_facet shared : ExternLib => FilePath

/-- A external library's dynlib. -/
builtin_facet dynlib : ExternLib => Dynlib

/-- The default facet for an input file. Produces the file path. -/
builtin_facet default : InputFile => FilePath

/--
The default facet for an input directory.
Produces the matching files in the directory.
-/
builtin_facet default : InputDir => Array FilePath
