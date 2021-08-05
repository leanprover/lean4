/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Dany Fabian
-/
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Data.Json.FromToJson

namespace Lean.Elab.Deriving.FromToJson
open Lean.Elab.Command
open Lean.Json
open Lean.Parser.Term
open Lean.Meta

def mkJsonField (n : Name) : Bool × Syntax :=
  let s  := n.toString
  let s₁ := s.dropRightWhile (· == '?')
  (s != s₁, Syntax.mkStrLit s₁)

def mkToJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 then
    if (← isStructure (← getEnv) declNames[0]) then
      let cmds ← liftTermElabM none <| do
        let ctx ← mkContext "toJson" declNames[0]
        let header ← mkHeader ctx ``ToJson 1 ctx.typeInfos[0]
        let fields := getStructureFieldsFlattened (← getEnv) declNames[0] (includeSubobjectFields := false)
        let fields : Array Syntax ← fields.mapM fun field => do
          let (isOptField, nm) ← mkJsonField field
          if isOptField then `(opt $nm $(mkIdent <| header.targetNames[0] ++ field))
          else `([($nm, toJson $(mkIdent <| header.targetNames[0] ++ field))])
        let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* :=
          mkObj <| List.join [$fields,*])
        return #[cmd] ++ (← mkInstanceCmds ctx ``ToJson declNames)
      cmds.forM elabCommand
      return true
    else
      let indVal ← getConstInfoInduct declNames[0]
      let cmds ← liftTermElabM none <| do
        let ctx ← mkContext "toJson" declNames[0]
        let toJsonFuncId := mkIdent ctx.auxFunNames[0]
        -- Return syntax to JSONify `id`, either via `ToJson` or recursively
        -- if `id`'s type is the type we're deriving for.
        let mkToJson (id : Syntax) (type : Expr) : TermElabM Syntax := do
          if type.isAppOf indVal.name then `($toJsonFuncId:ident $id:ident)
          else `(toJson $id:ident)
        let header ← mkHeader ctx ``ToJson 1 ctx.typeInfos[0]
        let discrs ← mkDiscrs header indVal
        let alts ← mkAlts indVal fun ctor args userNames => do
          match args, userNames with
          | #[], _ => `(toJson $(quote ctor.name.getString!))
          | #[(x, t)], none => `(mkObj [($(quote ctor.name.getString!), $(← mkToJson x t))])
          | xs, none =>
            let xs ← xs.mapM fun (x, t) => mkToJson x t
            `(mkObj [($(quote ctor.name.getString!), Json.arr #[$[$xs:term],*])])
          | xs, some userNames =>
            let xs ← xs.mapIdxM fun idx (x, t) => do
              `(($(quote userNames[idx].getString!), $(← mkToJson x t)))
            `(mkObj [($(quote ctor.name.getString!), mkObj [$[$xs:term],*])])
        let mut auxCmd ← `(match $[$discrs],* with $alts:matchAlt*)
        if ctx.usePartial then
          let letDecls ← mkLocalInstanceLetDecls ctx ``ToJson header.argNames
          auxCmd ← mkLet letDecls auxCmd
          auxCmd ← `(private partial def $toJsonFuncId:ident $header.binders:explicitBinder* := $auxCmd)
        else
          auxCmd ← `(private def $toJsonFuncId:ident $header.binders:explicitBinder* := $auxCmd)
        return #[auxCmd] ++ (← mkInstanceCmds ctx ``ToJson declNames)
      cmds.forM elabCommand
      return true
  else
    return false
where
  mkAlts
    (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Syntax × Expr) → (Option $ Array Name) → TermElabM Syntax) : TermElabM (Array Syntax) := do
  indVal.ctors.toArray.mapM fun ctor => do
    let ctorInfo ← getConstInfoCtor ctor
    forallTelescopeReducing ctorInfo.type fun xs type => do
      let mut patterns := #[]
      -- add `_` pattern for indices
      for i in [:indVal.numIndices] do
        patterns := patterns.push (← `(_))
      let mut ctorArgs := #[]
      -- add `_` for inductive parameters, they are inaccessible
      for i in [:indVal.numParams] do
        ctorArgs := ctorArgs.push (← `(_))
      -- bound constructor arguments and their types
      let mut binders := #[]
      let mut userNames := #[]
      for i in [:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]
        let localDecl ← getLocalDecl x.fvarId!
        if !localDecl.userName.hasMacroScopes then
          userNames := userNames.push localDecl.userName
        let a := mkIdent (← mkFreshUserName `a)
        binders := binders.push (a, localDecl.type)
        ctorArgs := ctorArgs.push a
      patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
      let rhs ← rhs ctorInfo binders (if userNames.size == binders.size then some userNames else none)
      `(matchAltExpr| | $[$patterns:term],* => $rhs:term)

def mkFromJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 then
    if (← isStructure (← getEnv) declNames[0]) then
      let cmds ← liftTermElabM none <| do
        let ctx ← mkContext "fromJson" declNames[0]
        let header ← mkHeader ctx ``FromJson 0 ctx.typeInfos[0]
        let fields := getStructureFieldsFlattened (← getEnv) declNames[0] (includeSubobjectFields := false)
        let jsonFields := fields.map (Prod.snd ∘ mkJsonField)
        let fields := fields.map mkIdent
        let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* (j : Json)
          : Except String $(← mkInductiveApp ctx.typeInfos[0] header.argNames) := do
          $[let $fields:ident ← getObjValAs? j _ $jsonFields]*
          return { $[$fields:ident := $(id fields)]* })
        return #[cmd] ++ (← mkInstanceCmds ctx ``FromJson declNames)
      cmds.forM elabCommand
      return true
    else
      let indVal ← getConstInfoInduct declNames[0]
      let cmds ← liftTermElabM none <| do
        let ctx ← mkContext "fromJson" declNames[0]
        let header ← mkHeader ctx ``FromJson 0 ctx.typeInfos[0]
        let fromJsonFuncId := mkIdent ctx.auxFunNames[0]
        let discrs ← mkDiscrs header indVal
        let alts ← mkAlts indVal fromJsonFuncId
        let mut auxCmd ← alts.foldrM (fun xs x => `(Except.orElseLazy $xs (fun _ => $x))) (←`(Except.error "no inductive constructor matched"))
        if ctx.usePartial then
          let letDecls ← mkLocalInstanceLetDecls ctx ``FromJson header.argNames
          auxCmd ← mkLet letDecls auxCmd
        -- FromJson is not structurally recursive even non-nested recursive inductives,
        -- so we also use `partial` then.
        if ctx.usePartial || indVal.isRec then
          auxCmd ← `(
            private partial def $fromJsonFuncId:ident $header.binders:explicitBinder* (json : Json)
                : Except String $(← mkInductiveApp ctx.typeInfos[0] header.argNames) :=
              $auxCmd)
        else
          auxCmd ← `(
            private def $fromJsonFuncId:ident $header.binders:explicitBinder* (json : Json)
                : Except String $(← mkInductiveApp ctx.typeInfos[0] header.argNames) :=
              $auxCmd)
        return #[auxCmd] ++ (← mkInstanceCmds ctx ``FromJson declNames)
      cmds.forM elabCommand
      return true
  else
    return false
where
  mkAlts (indVal : InductiveVal) (fromJsonFuncId : Syntax) : TermElabM (Array Syntax) := do
  let alts ←
    indVal.ctors.toArray.mapM fun ctor => do
      let ctorInfo ← getConstInfoCtor ctor
      forallTelescopeReducing ctorInfo.type fun xs type => do
        let mut binders := #[]
        let mut userNames := #[]
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]
          let localDecl ← getLocalDecl x.fvarId!
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)

        -- Return syntax to parse `id`, either via `FromJson` or recursively
        -- if `id`'s type is the type we're deriving for.
        let mkFromJson (idx : Nat) (type : Expr) : TermElabM Syntax :=
          if type.isAppOf indVal.name then `(Lean.Parser.Term.doExpr| $fromJsonFuncId:ident jsons[$(quote idx)])
          else `(Lean.Parser.Term.doExpr| fromJson? jsons[$(quote idx)])
        let identNames := binders.map Prod.fst
        let fromJsons ← binders.mapIdxM fun idx (_, type) => mkFromJson idx type

        let userNamesOpt ←
          if binders.size == userNames.size then
            `(some #[$[$(userNames.map quote):ident],*])
          else `(none)
        let stx ←
          `((Json.parseTagged json $(quote ctor.getString!) $(quote ctorInfo.numFields) $(quote userNamesOpt)).bind
            (fun jsons => do
              $[let $identNames:ident ← $fromJsons]*
              return $(mkIdent ctor):ident $identNames*))
        (stx, ctorInfo.numFields)
  -- the smaller cases, especially the ones without fields are likely faster
  let alts := alts.qsort (fun (_, x) (_, y) => x < y)
  alts.map Prod.fst

builtin_initialize
  registerBuiltinDerivingHandler ``ToJson mkToJsonInstanceHandler
  registerBuiltinDerivingHandler ``FromJson mkFromJsonInstanceHandler

end Lean.Elab.Deriving.FromToJson
