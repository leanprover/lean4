/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Init.Prelude

open Lean (Name)

namespace Lake

/-- The keyword for package declarations. -/
@[reducible] def Package.keyword : Name := `package

/-- The kind identifier for facets of a package. -/
@[match_pattern] abbrev Package.facetKind : Name := keyword

/--
The would-be keyword for module declarations.

Such declarations do not currently exist, but this is used
as the facet kind for modules.
-/
@[reducible] def Module.keyword : Name := `module

/-- The kind identifier for facets of a (Lean) module. -/
@[match_pattern] abbrev Module.facetKind : Name := keyword

/-- The keyword for Lean library declarations. -/
@[reducible] def LeanLib.keyword : Name := `lean_lib

/-- The kind identifier for facets of a Lean library. -/
@[match_pattern] abbrev LeanLib.facetKind : Name := `lean_lib

/-- The type kind for Lean library configurations. -/
@[match_pattern] abbrev LeanLib.configKind := facetKind

/-- The keyword for Lean executable declarations. -/
@[reducible] def LeanExe.keyword : Name := `lean_exe

/-- The kind identifier for facets of a Lean executable. -/
@[match_pattern] abbrev LeanExe.facetKind : Name := keyword

/-- The type kind for Lean executable configurations. -/
@[match_pattern] abbrev LeanExe.configKind := facetKind

/-- The keyword for external library declarations. -/
@[reducible] def ExternLib.keyword : Name := `extern_lib

/-- The kind identifier for facets of an external library. -/
@[match_pattern] abbrev ExternLib.facetKind : Name := keyword

/-- The type kind for external library configurations. -/
@[match_pattern] abbrev ExternLib.configKind := facetKind

/-- The keyword for input file declarations. -/
@[reducible] def InputFile.keyword : Name := `input_file

/-- The kind identifier for facets of an input file. -/
@[match_pattern] abbrev InputFile.facetKind := keyword

/-- The type kind for input file configurations. -/
@[match_pattern] abbrev InputFile.configKind := facetKind

/-- The keyword for input directory declarations. -/
@[reducible] def InputDir.keyword : Name := `input_dir

/-- Tge kind identifier for facets of an input directory. -/
@[match_pattern] abbrev InputDir.facetKind := keyword

/-- The type kind for input directory configurations. -/
@[match_pattern] abbrev InputDir.configKind := facetKind

/--
**Lake Internal.**
Returns the facet kind for an Lake target namespace.
Used by the `builtin_facet` macro.
-/
def facetKindForNamespace (ns : Name) : Name :=
  match ns with
  | `Lake.Package => Package.facetKind
  | `Lake.Module => Module.facetKind
  | `Lake.LeanLib => LeanLib.facetKind
  | `Lake.LeanExe => LeanExe.facetKind
  | `Lake.ExternLib => ExternLib.facetKind
  | `Lake.InputFile => InputFile.facetKind
  | `Lake.InputDir => InputDir.facetKind
  | _ => Name.anonymous
