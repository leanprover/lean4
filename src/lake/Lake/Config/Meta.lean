/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Util.Name
import Lake.Util.Binder

open Lean Syntax Parser Command

namespace Lake

structure ConfigProj (σ : Type u) (α : Type v) where
  get (cfg : σ) : α
  set (val : α) (cfg : σ) : σ
  modify (f : α → α) (cfg : σ) : σ

class ConfigField (σ : Type u) (name : Name) (α : outParam $ Type v) extends ConfigProj σ α where
  --status : DeprecationStatus := .none
  mkDefault? : σ → Option α := fun _ => none

class ConfigParent (σ : Type u) (ρ : semiOutParam $ Type v) extends ConfigProj σ ρ

instance [parent : ConfigParent σ ρ] [field : ConfigField ρ name α] : ConfigField σ name α where
  mkDefault? s := field.mkDefault? (parent.get s)
  get s := field.get (parent.get s)
  set a := parent.modify (field.set a)
  modify f := parent.modify (field.modify f)

abbrev FieldMap (α : Type u) (β : Name → Type v) :=
  DNameMap fun name => ConfigField α name (β name)

syntax configField :=
  atomic(nestedDeclModifiers ident) declSig (" := " term)?

/--
An tailored `structure` command for producing Lake configuration data types.
It supports additional field annotations and generates additional metadata used
during serialization to/from Lean and TOML.

It is not a perfect superset of `structure`, but instead just the parts
that are / could be reasonably needed by Lake.
-/
scoped syntax (name := configDecl)
  declModifiers "configuration " declId
  ppIndent((ppSpace bracketedBinder)* Term.optType «extends»?)
  ((" := " <|> " where ") (structCtor)? manyIndent(ppLine colGe ppGroup(configField)))?
  optDeriving
: command

instance : Coe Ident (TSyntax ``Term.structInstLVal) where
  coe stx := Unhygienic.run `(Term.structInstLVal| $stx:ident)

private structure FieldView where
  ref : Syntax
  mods : TSyntax ``Command.declModifiers := Unhygienic.run `(declModifiers|)
  id : Ident
  idLit : Term := quote id.getId
  type : Term
  defVal? : Option Term := none
  decl? : Option (TSyntax ``structSimpleBinder) := none
  parent  : Bool := false

private def mkFieldType (id : Ident) (views : Array FieldView) : MacroM Command := do
  let typeAlts ← views.mapM fun {idLit, type, ..} =>
    `(Term.matchAltExpr| | $idLit => $type)
  let catchAlt ← `(Term.matchAltExpr| | _ => PEmpty)
  let alts := typeAlts.push catchAlt
  `(abbrev $id (name : Name) := match name with $[$alts:matchAlt]*)

private structure FieldMetadata where
  insts : Array Command := #[]
  map : Term := Unhygienic.run `(DNameMap.empty)

private def mkConfigAuxDecls
  (structId : Ident) (structTy : Term) (views : Array FieldView)
: MacroM (Array Command) := do
  let data : FieldMetadata := {}
  -- `..` is used to avoid missing pattern error from an incomplete match.
  -- Such errors are too verbose, so we prefer errors on use of the missing field.
  let structPat ← `({$[$(views.map (·.id)):ident],* ..})
  let data ← views.foldlM (init := data) fun data view => do
    let {id, idLit, type, defVal?, parent, ..} := view
    let instId := mkIdentFrom id <| id.getId.modifyBase (structId.getId ++ ·.str "instConfigField")
    let defVal := Unhygienic.run do if let some val := defVal? then `(some $val) else `(none)
    let inst ← `(
      instance $instId:ident : ConfigField $structTy $idLit $type where
        mkDefault? := fun $structPat => $defVal
        get cfg := cfg.$id
        set val cfg := {cfg with $id := val}
        modify f cfg := {cfg with $id := f cfg.$id}
    )
    let data := {data with insts := data.insts.push inst}
    let data ←
      if parent then
        let instId' := mkIdentFrom id <| id.getId.modifyBase (structId.getId ++ ·.str "instConfigParent")
        let inst ← `(
          instance $instId':ident : ConfigParent $structTy $type := ⟨$(instId).toConfigProj⟩
        )
        pure {data with insts := data.insts.push inst}
      else
        pure data
    let map ← withRef data.map `($(data.map) |>.insert $idLit $instId)
    let data := {data with map := map}
    return data
  let typeId := mkIdentFrom structId <| structId.getId.modifyBase (·.str "FieldType")
  let fieldType ← mkFieldType typeId views
  let mapId := mkIdentFrom structId <| structId.getId.modifyBase (·.str "fieldMap")
  let map ← `(def $mapId : FieldMap $structTy $typeId := $(data.map))
  return data.insts |>.push fieldType |>.push map

private def mkFieldView (stx : TSyntax ``configField) : MacroM FieldView := withRef stx do
  let `(configField|$mods:declModifiers $id $bs* : $rty $[:= $val?]?) := stx
    | Macro.throwError "ill-formed configuration field declaration"
  let bvs ← expandBinders bs
  let type := mkDepArrow bvs rty
  --let type := mkCApp ``Option #[type]
  let defVal? ← val?.mapM fun val =>
    if bvs.isEmpty then pure val else `(fun $(bvs.map (·.id))* => $val)
  let decl ← `(structSimpleBinder|$mods:declModifiers $id : $type $[:= $defVal?]?)
  return {ref := stx, mods, id, type, defVal?, decl? := decl}

private def mkParentFieldView (stx : TSyntax ``structParent) : MacroM FieldView := withRef stx do
  let `(structParent|$[$id? :]? $type) := stx
    | Macro.throwError "ill-formed parent"
  let id ← do
    if let some id := id? then
      pure id
    else
      let typeId ←
        match type with
        | `($id:ident) => pure id
        | `($id:ident $(_)*) => pure id
        | _ => Macro.throwErrorAt type "unsupported parent syntax"
      pure <| mkIdentFrom typeId <| typeId.getId.modifyBase fun typeName =>
        Name.mkSimple s!"to{typeName.getString!}"
  return {ref := stx, id, type, parent := true}

@[macro configDecl]
def expandConfigDecl : Macro := fun stx => do
  let `($mods:declModifiers configuration%$tk $declId $bs* $[$ty?]?
      $[extends $ps?,* $[$xty?]?]? $[where $[$ctor?]? $fs?*]? $drv) := stx
    | Macro.throwError "ill-formed configuration declaration"
  withRef tk do
  let bvs ← expandBinders bs
  let structId : Ident := ⟨declId.raw[0]⟩
  let structTy := Syntax.mkApp structId (bvs.map (⟨·.mkArgument⟩))
  let views : Array FieldView ← (fs?.getD #[]).mapM mkFieldView
  let ps := ps?.getD <| TSepArray.mk #[]
  let views ← ps.getElems.foldlM (init := views) (·.push <$> mkParentFieldView ·)
  let fields := views.filterMap (·.decl?)
  let struct ← `($mods:declModifiers structure $declId $bs* $[$ty?]?
    extends $ps,* $(xty?.join)? where $(ctor?.join)? $fields* $drv:optDeriving)
  let auxDecls ← mkConfigAuxDecls structId structTy views
  let cmds := #[struct] ++ auxDecls
  return mkNullNode cmds
