/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Data
import Lake.Build.TargetTypes

/-!
# Simple Builtin Facet Declarations

This module declares most of the builtin facets an targets and
their build data builtin facets and targets. Some of these definitions
are needed for  configurations, so we define them here before we need to
import said configurations for `BuildInfo`.
-/

namespace Lake

-- ## Module Facets

/-- A module facet name along with proof of its data type. -/
structure ModuleFacet (α) where
  /-- The name of the module facet. -/
  name : WfName
  /-- Proof that module's facet build result is of type α. -/
  data_eq : ModuleData name = α
  deriving Repr

instance (facet : ModuleFacet α) : FamilyDef ModuleData facet.name α :=
  ⟨facet.data_eq⟩

instance [FamilyDef ModuleData facet α] : CoeDep WfName facet (ModuleFacet α) :=
  ⟨facet, family_key_eq_type⟩

namespace Module
abbrev leanBinFacet  := &`lean.bin
abbrev oleanFacet    := &`olean
abbrev ileanFacet    := &`ilean
abbrev cFacet        := &`lean.c
abbrev oFacet        := &`lean.o
abbrev dynlibFacet   := &`dynlib
end Module

/--
The core compilation / elaboration of the Lean file via `lean`,
which produce the Lean binaries of the module (i.e., `olean` and `ilean`).
It is thus the facet used by default for building imports of a module.
Also, if the module is not lean-only, it produces `c` files as well.
-/
module_data lean.bin : ActiveOpaqueTarget

/-- The `olean` file produced by `lean`  -/
module_data olean : ActiveFileTarget

/-- The `ilean` file produced by `lean` -/
module_data ilean : ActiveFileTarget

/-- The C file built from the Lean file via `lean` -/
module_data lean.c : ActiveFileTarget

/-- The object file built from `lean.c` -/
module_data lean.o : ActiveFileTarget

/-- Shared library for `--load-dynlib` -/
module_data dynlib : ActiveFileTarget

-- ## Package Facets

/-- The package's `extraDepTarget`. -/
package_data extraDep : ActiveOpaqueTarget

-- ## Target Facets

abbrev LeanLib.staticFacet := &`leanLib.static
abbrev LeanLib.sharedFacet := &`leanLib.shared
abbrev LeanExe.facet := &`leanExe
abbrev ExternLib.staticFacet := &`externLib.static
abbrev ExternLib.sharedFacet := &`externLib.shared

/-- A Lean library's static binary. -/
target_data leanLib.static : ActiveFileTarget

/-- A Lean library's shared binary. -/
target_data leanLib.shared : ActiveFileTarget

/-- A Lean binary executable. -/
target_data leanExe : ActiveFileTarget

/-- A external library's static binary. -/
target_data externLib.static : ActiveFileTarget

/-- A external library's shared binary. -/
target_data externLib.shared : ActiveFileTarget
