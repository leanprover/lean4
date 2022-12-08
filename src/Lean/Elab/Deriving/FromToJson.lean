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

def mkJsonField (n : Name) : CoreM (Bool × Term) := do
  let .str .anonymous s := n | throwError "invalid json field name {n}"
  let s₁ := s.dropRightWhile (· == '?')
  return (s != s₁, Syntax.mkStrLit s₁)

def mkToJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 then
    if isStructure (← getEnv) declNames[0]! then
      let cmds ← liftTermElabM do
        let ctx ← mkContext "toJson" declNames[0]!
        let header ← mkHeader ``ToJson 1 ctx.typeInfos[0]!
        let fields := getStructureFieldsFlattened (← getEnv) declNames[0]! (includeSubobjectFields := false)
        let fields ← fields.mapM fun field => do
          let (isOptField, nm) ← mkJsonField field
          let target := mkIdent header.targetNames[0]!
          if isOptField then ``(opt $nm ($target).$(mkIdent field))
          else ``([($nm, toJson ($target).$(mkIdent field))])
        let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]!):ident $header.binders:bracketedBinder* : Json :=
          mkObj <| List.join [$fields,*])
        return #[cmd] ++ (← mkInstanceCmds ctx ``ToJson declNames)
      cmds.forM elabCommand
      return true
    else
      let indVal ← getConstInfoInduct declNames[0]!
      let cmds ← liftTermElabM do
        let ctx ← mkContext "toJson" declNames[0]!
        let toJsonFuncId := mkIdent ctx.auxFunNames[0]!
        -- Return syntax to JSONify `id`, either via `ToJson` or recursively
        -- if `id`'s type is the type we're deriving for.
        let mkToJson (id : Ident) (type : Expr) : TermElabM Term := do
          if type.isAppOf indVal.name then `($toJsonFuncId:ident $id:ident)
          else ``(toJson $id:ident)
        let header ← mkHeader ``ToJson 1 ctx.typeInfos[0]!
        let discrs ← mkDiscrs header indVal
        let alts ← mkAlts indVal fun ctor args userNames => do
          let ctorStr := ctor.name.eraseMacroScopes.getString!
          match args, userNames with
          | #[], _ => ``(toJson $(quote ctorStr))
          | #[(x, t)], none => ``(mkObj [($(quote ctorStr), $(← mkToJson x t))])
          | xs, none =>
            let xs ← xs.mapM fun (x, t) => mkToJson x t
            ``(mkObj [($(quote ctorStr), Json.arr #[$[$xs:term],*])])
          | xs, some userNames =>
            let xs ← xs.mapIdxM fun idx (x, t) => do
              `(($(quote userNames[idx]!.eraseMacroScopes.getString!), $(← mkToJson x t)))
            ``(mkObj [($(quote ctorStr), mkObj [$[$xs:term],*])])
        let auxTerm ← `(match $[$discrs],* with $alts:matchAlt*)
        let auxCmd ←
          if ctx.usePartial then
            let letDecls ← mkLocalInstanceLetDecls ctx ``ToJson header.argNames
            let auxTerm ← mkLet letDecls auxTerm
            `(private partial def $toJsonFuncId:ident $header.binders:bracketedBinder* : Json := $auxTerm)
          else
            `(private def $toJsonFuncId:ident $header.binders:bracketedBinder* : Json := $auxTerm)
        return #[auxCmd] ++ (← mkInstanceCmds ctx ``ToJson declNames)
      cmds.forM elabCommand
      return true
  else
    return false
where
  mkAlts
    (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term) : TermElabM (Array (TSyntax ``matchAlt)) := do
  indVal.ctors.toArray.mapM fun ctor => do
    let ctorInfo ← getConstInfoCtor ctor
    forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut patterns := #[]
      -- add `_` pattern for indices
      for _ in [:indVal.numIndices] do
        patterns := patterns.push (← `(_))
      let mut ctorArgs := #[]
      -- add `_` for inductive parameters, they are inaccessible
      for _ in [:indVal.numParams] do
        ctorArgs := ctorArgs.push (← `(_))
      -- bound constructor arguments and their types
      let mut binders := #[]
      let mut userNames := #[]
      for i in [:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]!
        let localDecl ← x.fvarId!.getDecl
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
    let declName := declNames[0]!
    if isStructure (← getEnv) declName then
      let cmds ← liftTermElabM do
        let ctx ← mkContext "fromJson" declName
        let header ← mkHeader ``FromJson 0 ctx.typeInfos[0]!
        let fields := getStructureFieldsFlattened (← getEnv) declName (includeSubobjectFields := false)
        let getters ← fields.mapM (fun field => do
          let getter ← `(getObjValAs? j _ $(Prod.snd <| ← mkJsonField field))
          let getter ← `(doElem| Except.mapError (fun s => (toString $(quote declName)) ++ "." ++ (toString $(quote field)) ++ ": " ++ s) <| $getter)
          return getter
        )
        let fields := fields.map mkIdent
        let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]!):ident $header.binders:bracketedBinder* (j : Json)
          : Except String $(← mkInductiveApp ctx.typeInfos[0]! header.argNames) := do
          $[let $fields:ident ← $getters]*
          return { $[$fields:ident := $(id fields)],* })
        return #[cmd] ++ (← mkInstanceCmds ctx ``FromJson declNames)
      cmds.forM elabCommand
      return true
    else
      let indVal ← getConstInfoInduct declName
      let cmds ← liftTermElabM do
        let ctx ← mkContext "fromJson" declName
        let header ← mkHeader ``FromJson 0 ctx.typeInfos[0]!
        let fromJsonFuncId := mkIdent ctx.auxFunNames[0]!
        let alts ← mkAlts indVal fromJsonFuncId
        let mut auxTerm ← alts.foldrM (fun xs x => `(Except.orElseLazy $xs (fun _ => $x))) (← `(Except.error "no inductive constructor matched"))
        if ctx.usePartial then
          let letDecls ← mkLocalInstanceLetDecls ctx ``FromJson header.argNames
          auxTerm ← mkLet letDecls auxTerm
        -- FromJson is not structurally recursive even non-nested recursive inductives,
        -- so we also use `partial` then.
        let auxCmd ←
          if ctx.usePartial || indVal.isRec then
            `(private partial def $fromJsonFuncId:ident $header.binders:bracketedBinder* (json : Json)
                  : Except String $(← mkInductiveApp ctx.typeInfos[0]! header.argNames) :=
                $auxTerm)
          else
            `(private def $fromJsonFuncId:ident $header.binders:bracketedBinder* (json : Json)
                  : Except String $(← mkInductiveApp ctx.typeInfos[0]! header.argNames) :=
                $auxTerm)
        return #[auxCmd] ++ (← mkInstanceCmds ctx ``FromJson declNames)
      cmds.forM elabCommand
      return true
  else
    return false
where
  mkAlts (indVal : InductiveVal) (fromJsonFuncId : Ident) : TermElabM (Array Term) := do
  let alts ←
    indVal.ctors.toArray.mapM fun ctor => do
      let ctorInfo ← getConstInfoCtor ctor
      forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut binders := #[]
        let mut userNames := #[]
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)

        -- Return syntax to parse `id`, either via `FromJson` or recursively
        -- if `id`'s type is the type we're deriving for.
        let mkFromJson (idx : Nat) (type : Expr) : TermElabM (TSyntax ``doExpr) :=
          if type.isAppOf indVal.name then `(Lean.Parser.Term.doExpr| $fromJsonFuncId:ident jsons[$(quote idx)]!)
          else `(Lean.Parser.Term.doExpr| fromJson? jsons[$(quote idx)]!)
        let identNames := binders.map Prod.fst
        let fromJsons ← binders.mapIdxM fun idx (_, type) => mkFromJson idx type
        let userNamesOpt ← if binders.size == userNames.size then
          ``(some #[$[$(userNames.map quote)],*])
        else
          ``(none)
        let stx ←
          `((Json.parseTagged json $(quote ctor.eraseMacroScopes.getString!) $(quote ctorInfo.numFields) $(quote userNamesOpt)).bind
            (fun jsons => do
              $[let $identNames:ident ← $fromJsons:doExpr]*
              return $(mkIdent ctor):ident $identNames*))
        pure (stx, ctorInfo.numFields)
  -- the smaller cases, especially the ones without fields are likely faster
  let alts := alts.qsort (fun (_, x) (_, y) => x < y)
  return alts.map Prod.fst

builtin_initialize
  registerDerivingHandler ``ToJson mkToJsonInstanceHandler
  registerDerivingHandler ``FromJson mkFromJsonInstanceHandler

end Lean.Elab.Deriving.FromToJson
