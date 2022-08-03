/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Job
import Lake.Build.Data

/-!
# Simple Builtin Facet Declarations

This module declares most of the builtin facets an targets and
their build data builtin facets and targets. Some of these definitions
are needed for configurations, so we define them here before we need to
import said configurations for `BuildInfo`.
-/

namespace Lake
export System (FilePath)

/--
A dynamic/shared library for linking.
Represented by an optional `-L` library directory × a `-l` library name.
-/
abbrev Dynlib := Option FilePath × String

/-! ## Module Facets -/

/-- A module facet name along with proof of its data type. -/
structure ModuleFacet (α) where
  /-- The name of the module facet. -/
  name : Name
  /-- Proof that module's facet build result is of type α. -/
  data_eq : ModuleData name = α
  deriving Repr

instance (facet : ModuleFacet α) : FamilyDef ModuleData facet.name α :=
  ⟨facet.data_eq⟩

instance [FamilyDef ModuleData facet α] : CoeDep Name facet (ModuleFacet α) :=
  ⟨facet, family_key_eq_type⟩

/--
The core compilation / elaboration of the Lean file via `lean`,
which produce the Lean binaries of the module (i.e., `olean` and `ilean`).
It is thus the facet used by default for building imports of a module.
Also, if the module is not lean-only, it produces `c` files as well.
-/
abbrev Module.leanBinFacet := `bin
module_data bin : BuildJob Unit

/-- The `olean` file produced by `lean`  -/
abbrev Module.oleanFacet := `olean
module_data olean : BuildJob FilePath

/-- The `ilean` file produced by `lean` -/
abbrev Module.ileanFacet := `ilean
module_data ilean : BuildJob FilePath

/-- The C file built from the Lean file via `lean` -/
abbrev Module.cFacet := `c
module_data c : BuildJob FilePath

/-- The object file built from `lean.c` -/
abbrev Module.oFacet := `o
module_data o : BuildJob FilePath

/-- Shared library for `--load-dynlib`. Returns just the library name. -/
abbrev Module.dynlibFacet := `dynlib
module_data dynlib : BuildJob String

/-! ## Package Facets -/

/-- The package's cloud build release. -/
abbrev Package.releaseFacet := `release
package_data release : BuildJob Unit

/-- The package's `extraDepTarget` mixed with its transitive dependencies. -/
abbrev Package.extraDepFacet := `extraDep
package_data extraDep : BuildJob Unit

/-! ## Target Facets -/

/-- A Lean library's Lean libraries. -/
abbrev LeanLib.leanFacet := `lean
library_data lean : BuildJob Unit

/-- A Lean library's static binary. -/
abbrev LeanLib.staticFacet := `static
library_data static : BuildJob FilePath

/-- A Lean library's shared binary. -/
abbrev LeanLib.sharedFacet := `shared
library_data shared : BuildJob FilePath

/-- A Lean binary executable. -/
abbrev LeanExe.exeFacet := `leanExe
target_data leanExe : BuildJob FilePath

/-- A external library's static binary. -/
abbrev ExternLib.staticFacet := `externLib.static
target_data externLib.static : BuildJob FilePath

/-- A external library's shared binary. -/
abbrev ExternLib.sharedFacet := `externLib.shared
target_data externLib.shared : BuildJob FilePath

/-- A external library's dynlib. -/
abbrev ExternLib.dynlibFacet := `externLib.dynlib
target_data externLib.dynlib : BuildJob Dynlib
