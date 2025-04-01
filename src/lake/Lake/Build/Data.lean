/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Key
import Lake.Util.Family
import Lake.Config.Dynlib

open Lean
namespace Lake

--------------------------------------------------------------------------------
/-! ## Build Data Subtypes                                                    -/
--------------------------------------------------------------------------------

/--
The open type family which maps a Lake data kind to its associated type.
For example, `LeanLib.facetKind` maps to `LeanLib`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `data_type`).
-/
opaque DataType (kind : Name) : Type u

/-- A `Name` descriptor of a data type. -/
class DataKind (α : Type u) where
  /-- The name which describes `α`. -/
  name : Name
  /-- Proof that `α` is the data type described by `name`. -/
  wf : ¬ name.isAnonymous ∧ α = DataType name

/--
Tries to synthesize a `Name` descriptor of a data type.
Otherwise uses `Name.anonymous` to indicate none was found.
-/
class OptDataKind (α : Type u) where
  /-- The name which describes `α` (or `Name.anonymous` if none). -/
  name : Name
  /-- Proof that `α` is the data type described by `name` (if valid). -/
  wf (h : ¬ name.isAnonymous) : α = DataType name

@[instance low]
def OptDataKind.anonymous : OptDataKind α where
  name := .anonymous
  wf h := by simp [Name.isAnonymous] at h

instance : Inhabited (OptDataKind α) := ⟨OptDataKind.anonymous⟩

@[inline] def OptDataKind.isAnonymous (self : OptDataKind α) : Bool :=
  self.name.isAnonymous

theorem OptDataKind.eq_data_type
  {self : OptDataKind α} (h : ¬ self.isAnonymous) : α = DataType self.name
:= self.wf h

instance [DataKind α] : OptDataKind α where
  name := DataKind.name α
  wf _ := DataKind.wf.2

instance : CoeOut (OptDataKind α) Lean.Name := ⟨(·.name)⟩
instance : ToString (OptDataKind α) := ⟨(·.name.toString)⟩

@[deprecated DataType (since := "2025-03-26")] abbrev TargetData := DataType

/--
The open type family which maps a Lake facet to its output type.
For example, a `FilePath` for the `module.olean` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `facet_data`).
-/
opaque FacetOut (facet : Name) : Type

/--
The open type family which maps a Lake facet kind and name to its output type.
For example, a `FilePath` for the `module` `olean` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `facet_data`).
-/
abbrev FacetData (kind facet : Name) := FacetOut (kind ++ facet)

instance [h : FamilyDef FacetOut (kind ++ facet) α] : FamilyDef (FacetData kind) facet α :=
  ⟨h.fam_eq⟩

instance [h :  FamilyDef (FacetData kind) facet α] : FamilyDef FacetOut (kind ++ facet) α :=
  ⟨h.fam_eq⟩

/--
The open type family which maps a module facet's name to its output type.
For example, a `FilePath` for the module `olean` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
abbrev ModuleData := FacetData Module.facetKind

/--
The open type family which maps a package facet's name to output type.
For example, an `Arrry Package` of direct dependencies for the `deps` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
abbrev PackageData := FacetData Package.facetKind

/--
The open type family which maps a Lean library facet's name to its output type.
For example, the `FilePath` pf the generated static library for the `static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `library_data`).
-/
abbrev LibraryData := FacetData LeanLib.facetKind

@[inherit_doc LibraryData]
abbrev LeanLibData := LibraryData

/--
The open type family which maps a custom package target
(package × target name) to its output type.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
opaque CustomOut (target : Name × Name) : Type

/--
The open type family which maps a custom package targetto its output type.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
abbrev CustomData (package target : Name) := CustomOut (package, target)

instance [h : FamilyDef CustomOut (p, t) α] : FamilyDef (CustomData p) t α :=
  ⟨h.fam_eq⟩

--------------------------------------------------------------------------------
/-! ## Build Data                                                             -/
--------------------------------------------------------------------------------

/--
A mapping between a build key and its associated build data in the store.
It is a simple type function composed of the separate open type families for
modules facets, package facets, Lake target facets, and custom targets.
-/
abbrev BuildData : BuildKey → Type
| .module _ => DataType Module.facetKind
| .package _ => DataType Package.facetKind
| .packageTarget p t => CustomData p t
| .facet _ f => FacetOut f

instance (priority := low) : FamilyDef BuildData (.packageTarget p t) (CustomData p t) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.facet t f) (FacetOut f) := ⟨rfl⟩

instance [FamilyOut (CustomData p) t α]
: FamilyDef BuildData (.packageTarget p t) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut DataType Module.facetKind α]
: FamilyDef BuildData (.module k) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut DataType Package.facetKind α]
: FamilyDef BuildData (.package k) α where
  fam_eq := by unfold BuildData; simp

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

open Parser Command

/-- Macro for declaring new `DatayType`. -/
scoped macro (name := dataTypeDecl)
  doc?:optional(docComment) "data_type " kind:ident " : " ty:term
: command => do
  let fam := mkCIdentFrom (← getRef) ``DataType
  let kindName := Name.quoteFrom kind kind.getId
  `($[$doc?]? family_def $kind : $fam $kindName := $ty
    instance : DataKind $ty := ⟨$kindName, by simp [Name.isAnonymous]⟩)

data_type unit : Unit
data_type bool : Bool
data_type filepath : System.FilePath
data_type dynlib : Dynlib

/-- Internal macro for declaring new facet within Lake. -/
scoped macro (name := builtinFacetCommand)
  doc?:optional(docComment) tk:"builtin_facet "
  id?:optional(atomic(group(ident " @ "))) name:ident " : " ns:ident " => " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom tk ``FacetOut
  let nsName :: _ ← Macro.resolveNamespace ns.getId
    | Macro.throwErrorAt ns s!"unknown or ambiguous target namespace '{ns.getId}'"
  let kindName := facetKindForNamespace nsName
  if kindName.isAnonymous then
    Macro.throwErrorAt ns s!"unknown target namespace '{ns.getId}'"
  let nameLit := Name.quoteFrom name name.getId (canonical := id?.isSome)
  let kindLit := Name.quoteFrom ns kindName (canonical := true)
  let facet := kindName ++ name.getId
  let facetId := mkIdentFrom tk facet (canonical := true)
  let facetLit := Name.quoteFrom tk facet
  let id ←
    if let some id := id? then
      let id := id.raw[0]
      pure <| mkIdentFrom id (ns.getId ++ id.getId) (canonical := true)
    else
      match name.getId with
      | .str .anonymous n => pure <| mkIdentFrom name (ns.getId.str s!"{n}Facet") (canonical := true)
      | _ =>  Macro.throwErrorAt name "cannot generate facet declaration name from facet name"
  `(
    $[$doc?]? @[reducible] def $id := $facetLit
    family_def $facetId : $fam $facetLit := $ty
    instance : FamilyDef FacetOut ($kindLit ++ $nameLit) $ty :=
      inferInstanceAs (FamilyDef FacetOut $facetLit $ty)
  )

/-- Macro for declaring new `FacetData`. -/
scoped macro (name := facetDataDecl)
  doc?:optional(docComment) tk:"facet_data " kind:ident name:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom tk ``FacetOut
  let kindLit := Name.quoteFrom kind kind.getId
  let nameLit := Name.quoteFrom name name.getId
  let facet := kind.getId ++ name.getId
  let facetLit := Name.quoteFrom tk facet
  let id := mkIdentFrom tk facet (canonical := true)
  `($[$doc?]? family_def $id : $fam $facetLit := $ty
    instance : FamilyDef FacetOut ($kindLit ++ $nameLit) $ty :=
      inferInstanceAs (FamilyDef FacetOut $facetLit $ty))

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl)
  doc?:optional(docComment) tk:"package_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data%$tk $(mkIdentFrom tk Package.facetKind) $facet : $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl)
  doc?:optional(docComment) tk:"module_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data%$tk $(mkIdentFrom tk Module.facetKind) $facet : $ty)

/-- Macro for declaring new `LibraryData`. -/
scoped macro (name := libraryDataDecl)
  doc?:optional(docComment) tk:"library_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data%$tk $(mkIdentFrom tk LeanLib.facetKind) $facet : $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl)
  doc?:optional(docComment) tk:"target_data " id:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom (← getRef) ``TargetData
  let idx := Name.quoteFrom id id.getId
  `($[$doc?]? family_def $id : $fam $idx := $ty)

/-- Macro for declaring new `CustomData`. -/
scoped macro (name := customDataDecl)
  doc?:optional(docComment) tk:"custom_data " pkg:ident tgt:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom (← getRef) ``CustomOut
  let id := mkIdentFrom tgt (pkg.getId ++ tgt.getId)
  let pkg := Name.quoteFrom pkg pkg.getId
  let tgt := Name.quoteFrom pkg tgt.getId
  `($[$doc?]? family_def $id : $fam ($pkg, $tgt) := $ty)
