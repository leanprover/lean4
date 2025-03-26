/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Data
import Lake.Build.Job.Basic
import Lake.Config.Dynlib

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

structure ModuleDeps where
  dynlibs : Array FilePath := #[]
  plugins : Array FilePath := #[]
  deriving Inhabited, Repr

/-! ## Module Facets -/

/-- A module facet name along with proof of its data type. -/
structure ModuleFacet (α) where
  /-- The name of the module facet. -/
  name : Name
  /-- Proof that module's facet build result is of type α. -/
  data_eq : FacetOut name = α
  deriving Repr

instance (facet : ModuleFacet α) : FamilyDef FacetOut facet.name α :=
  ⟨facet.data_eq⟩

instance [FamilyOut FacetOut facet α] : CoeDep Name facet (ModuleFacet α) :=
  ⟨facet, FamilyOut.fam_eq⟩

/--
The facet which builds all of a module's dependencies
(i.e., transitive local imports and `--load-dynlib` shared libraries).
Returns the list of shared libraries to load along with their search path.
-/
builtin_facet Module.depsFacet module deps : ModuleDeps

/--
The core build facet of a Lean file.
Elaborates the Lean file via `lean` and produces all the Lean artifacts
of the module (i.e., `olean`, `ilean`, `c`).
Its trace just includes its dependencies.
-/
builtin_facet Module.leanArtsFacet module leanArts : Unit

/-- The `olean` file produced by `lean`. -/
builtin_facet Module.oleanFacet module olean : FilePath

/-- The `ilean` file produced by `lean`. -/
builtin_facet Module.ileanFacet module ilean : FilePath

/-- The C file built from the Lean file via `lean`. -/
builtin_facet Module.cFacet module c : FilePath

/-- The LLVM BC file built from the Lean file via `lean`. -/
builtin_facet Module.bcFacet module bc : FilePath

/--
The object file `.c.o` built from `c`.
On Windows, this is `c.o.noexport`, on other systems it is `c.o.export`).
-/
builtin_facet Module.coFacet module c.o : FilePath

/-- The object file `.c.o.export` built from `c` (with `-DLEAN_EXPORTING`). -/
builtin_facet Module.coExportFacet module c.o.export : FilePath

/-- The object file `.c.o.noexport` built from `c` (without `-DLEAN_EXPORTING`). -/
builtin_facet Module.coNoExportFacet module c.o.noexport : FilePath

/-- The object file `.bc.o` built from `bc`. -/
builtin_facet Module.bcoFacet module bc.o : FilePath

/--
The object file built from `c`/`bc`.
On Windows with the C backend, no Lean symbols are exported.
On every other configuration, symbols are exported.
-/
builtin_facet Module.oFacet module o : FilePath

/-- The object file built from `c`/`bc` (with Lean symbols exported). -/
builtin_facet Module.oExportFacet module o.export : FilePath

/-- The object file built from `c`/`bc` (without Lean symbols exported). -/
builtin_facet Module.oNoExportFacet module o.noexport : FilePath


/-! ## Package Facets -/

/--
A package's *optional* cached build archive (e.g., from Reservoir or GitHub).
Will NOT cause the whole build to fail if the archive cannot be fetched.
-/
builtin_facet Package.optBuildCacheFacet package optCache : Bool

/--
A package's cached build archive (e.g., from Reservoir or GitHub).
Will cause the whole build to fail if the archive cannot be fetched.
-/
builtin_facet Package.buildCacheFacet package cache : Unit

/--
A package's *optional* build archive from Reservoir.
Will NOT cause the whole build to fail if the barrel cannot be fetched.
-/
builtin_facet Package.optReservoirBarrelFacet package optBarrel : Bool

/--
A package's Reservoir build archive from Reservoir.
Will cause the whole build to fail if the barrel cannot be fetched.
-/
builtin_facet Package.reservoirBarrelFacet package barrel : Unit

/--
A package's *optional* build archive from a GitHub release.
Will NOT cause the whole build to fail if the release cannot be fetched.
-/
builtin_facet Package.optGitHubReleaseFacet package optRelease : Bool

@[deprecated optGitHubReleaseFacet (since := "2024-09-27")]
abbrev Package.optReleaseFacet := optGitHubReleaseFacet

/--
A package's build archive from a GitHub release.
Will cause the whole build to fail if the release cannot be fetched.
-/
builtin_facet Package.gitHubReleaseFacet package release : Unit

@[deprecated gitHubReleaseFacet (since := "2024-09-27")]
abbrev Package.releaseFacet := gitHubReleaseFacet

/-- A package's `extraDepTargets` mixed with its transitive dependencies'. -/
builtin_facet Package.extraDepFacet package extraDep : Unit

/-! ## Target Facets -/

/-- A Lean library's Lean artifacts (i.e., `olean`, `ilean`, `c`). -/
builtin_facet LeanLib.leanArtsFacet leanLib leanArts : Unit

/-- A Lean library's static artifact. -/
builtin_facet LeanLib.staticFacet leanLib static : FilePath

/--
A Lean library's static artifact (with exported symbols).

Static libraries with explicit exports are built as thin libraries.
Such libraries are usually used as part of the local build process of some
shared artifact and not publicly distributed. Standard static libraries are
much better for distribution.
-/
builtin_facet LeanLib.staticExportFacet leanLib static.export : FilePath

/-- A Lean library's shared artifact. -/
builtin_facet LeanLib.sharedFacet leanLib shared : FilePath

/-- A Lean library's `extraDepTargets` mixed with its package's. -/
builtin_facet LeanLib.extraDepFacet leanLib extraDep : Unit

/-- A Lean binary executable. -/
builtin_facet LeanExe.exeFacet leanExe exe : FilePath

/-- A external library's static binary. -/
builtin_facet ExternLib.staticFacet externLib static : FilePath

/-- A external library's shared binary. -/
builtin_facet ExternLib.sharedFacet externLib shared : FilePath

/-- A external library's dynlib. -/
builtin_facet ExternLib.dynlibFacet externLib dynlib : Dynlib
