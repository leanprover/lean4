/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Binder
public import Lake.Config.MetaClasses
public meta import Lake.Util.Binder
public meta import Lean.Parser.Command
public meta import Lake.Util.Name
import Lean.Parser.Command

open Lean Syntax Parser Command

namespace Lake

public syntax configField :=
  atomic(nestedDeclModifiers atomic(ident " @ ")? ident,+) declSig (" := " term)?

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
  ids : Array Ident := #[id]
  type : Term
  defVal : Term
  decl? : Option (TSyntax ``structSimpleBinder) := none
  parent  : Bool := false

private structure FieldMetadata where
  cmds : Array Command := #[]
  fields : Term := Unhygienic.run `(Array.empty)

-- We automatically disable the following option for `macro`s but the subsequent `def`s both contain
-- quotations and are called only by `macro`s, so we disable the option for them manually.
set_option internal.parseQuotWithCurrentStage false

private meta def mkConfigAuxDecls
  (vis? : Option (TSyntax ``visibility))
  (structId : Ident) (structArity : Nat) (structTy : Term) (views : Array FieldView)
: MacroM (Array Command) := do
  let data : FieldMetadata := {}
  -- `..` is used to avoid missing pattern error from an incomplete match.
  -- Such errors are too verbose, so we prefer errors on use of the missing field.
  let structPat ← `({$[$(views.map (·.id)):ident],* ..})
  let data ← views.foldlM (init := data) fun {cmds, fields} view => do
    let {id, ids, type, defVal, parent, ..} := view
    let projId := mkIdentFrom id <| id.getId.modifyBase (structId.getId ++ · |>.str "_proj")
    let cmds ← cmds.push <$> `(
       $[$vis?:visibility]? def $projId:ident : ConfigProj $structTy $type where
        get cfg := cfg.$id
        set val cfg := {cfg with $id := val}
        modify f cfg := {cfg with $id := f cfg.$id}
        mkDefault := fun $structPat => $defVal
    )
    let realNameLit := Name.quoteFrom id id.getId
    if parent then
      let instId := mkIdentFrom id <| id.getId.modifyBase (structId.getId ++ · |>.str "instConfigParent")
      let cmds ← cmds.push <$> `(
        $[$vis?:visibility]? instance $instId:ident : ConfigParent $structTy $type := ⟨$projId⟩
      )
      let fields ← withRef fields `($(fields) |>.append (ConfigFields.fields $type))
      let fields ← withRef fields `($(fields) |>.push {
        name := $realNameLit
        realName := $realNameLit
        parent := true
        : ConfigFieldInfo
      })
      return {cmds, fields}
    else
      let data := {cmds, fields}
      let addName canonical data id := do
        let {cmds, fields} := data
        let nameLit := Name.quoteFrom id id.getId
        let instId := mkIdentFrom id <|
          id.getId.modifyBase (structId.getId ++ · |>.str "instConfigField")
        let cmds ← cmds.push <$> `(
           $[$vis?:visibility]? instance $instId:ident : ConfigField $structTy $nameLit $type := ⟨$projId⟩
        )
        let fields ← withRef fields `($(fields) |>.push {
          name := $nameLit
          realName := $realNameLit
          canonical := $(quote canonical)
          : ConfigFieldInfo
        })
        return {cmds, fields}
      if h : 0 < ids.size then
        let data ← addName true data (ids[0]'h)
        let data ← ids.foldlM (start := 1) (addName false) data
        return data
      else
        return data
  let fieldsId := mkIdentFrom structId <| structId.getId.modifyBase (·.str "_fields")
  let fieldsDef ← `( $[$vis?:visibility]? def $fieldsId:ident := $(data.fields))
  let instId := mkIdentFrom structId <| structId.getId.modifyBase (·.str "instConfigFields")
  let fieldsInst ← `( $[$vis?:visibility]? instance $instId:ident : ConfigFields $structTy := ⟨$fieldsId⟩)
  let instId := mkIdentFrom structId <| structId.getId.modifyBase (·.str "instConfigInfo")
  let structNameLit : Term := ⟨mkNode ``Term.doubleQuotedName #[mkAtom "`", mkAtom "`", structId]⟩
  let info ← `({fields := $fieldsId, arity := $(quote structArity)})
  let infoInst ← `( $[$vis?:visibility]? instance $instId:ident : ConfigInfo $structNameLit := $info)
  let instId := mkIdentFrom structId <| structId.getId.modifyBase (·.str "instEmptyCollection")
  let emptyInst ← `( $[$vis?:visibility]? instance $instId:ident : EmptyCollection $structTy := ⟨{}⟩)
  return data.cmds.push fieldsDef |>.push fieldsInst |>.push infoInst |>.push emptyInst

private meta def mkFieldView (stx : TSyntax ``configField) : MacroM FieldView := withRef stx do
  let `(configField|$mods:declModifiers $[$id? @]? $ids,* $bs* : $rty $[:= $val?]?) := stx
    | Macro.throwError "ill-formed configuration field declaration"
  let bvs ← expandBinders bs
  let type := mkDepArrow bvs rty
  let some id := id? <|> ids.getElems[0]?
    | Macro.throwError "expected a least one field name"
  withRef id.raw do
  let some val := val?
    | Macro.throwError "expected a default value"
  let defVal ← `(fun $(bvs.map (·.id))* => $val)
  let decl ← `(structSimpleBinder|$mods:declModifiers $id : $type := $defVal)
  return {ref := stx, mods, id, ids, type, defVal, decl? := decl}

private meta def mkParentFieldView (stx : TSyntax ``structParent) : MacroM FieldView := withRef stx do
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
  return {ref := stx, id, type, defVal := ← `(∅), parent := true}

@[macro configDecl]
public meta def expandConfigDecl : Macro := fun stx => do
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
  let struct ← `(
    $mods:declModifiers structure $declId $bs* $[$ty?]?
    extends $ps,* $(xty?.join)? where $(ctor?.join)? $fields* $drv:optDeriving
  )
  let vis? := mods.raw[2].getOptional?.map (⟨·⟩)
  let auxDecls ← mkConfigAuxDecls vis? structId bs.size structTy views
  let cmds := #[struct] ++ auxDecls
  return mkNullNode cmds
