/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Dany Fabian
-/
prelude
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Data.Json.FromToJson

namespace Lean.Elab.Deriving.FromToJson
open Lean.Elab.Command
open Lean.Json
open Lean.Parser.Term
open Lean.Meta

def mkToJsonHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ``ToJson 1 indVal

def mkFromJsonHeader (indVal : InductiveVal) : TermElabM Header := do
  let header ← mkHeader ``FromJson 0 indVal
  let jsonArg ← `(bracketedBinderF|(json : Json))
  return {header with
    binders := header.binders.push jsonArg}

def mkJsonField (n : Name) : CoreM (Bool × Term) := do
  let .str .anonymous s := n | throwError "invalid json field name {n}"
  let s₁ := s.dropRightWhile (· == '?')
  return (s != s₁, Syntax.mkStrLit s₁)

def mkToJsonBodyForStruct (header : Header) (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let fields ← fields.mapM fun field => do
    let (isOptField, nm) ← mkJsonField field
    let target := mkIdent header.targetNames[0]!
    if isOptField then ``(opt $nm $target.$(mkIdent field))
    else ``([($nm, toJson ($target).$(mkIdent field))])
  `(mkObj <| List.flatten [$fields,*])

def mkToJsonBodyForInduct (ctx : Context) (header : Header) (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let toJsonFuncId := mkIdent ctx.auxFunNames[0]!
  -- Return syntax to JSONify `id`, either via `ToJson` or recursively
  -- if `id`'s type is the type we're deriving for.
  let mkToJson (id : Ident) (type : Expr) : TermElabM Term := do
        if type.isAppOf indVal.name then `($toJsonFuncId:ident $id:ident)
        else ``(toJson $id:ident)
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
  `(match $[$discrs],* with $alts:matchAlt*)

where
  mkAlts
    (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term): TermElabM (Array (TSyntax ``matchAlt)) := do
      let mut alts := #[]
      for ctorName in indVal.ctors do
        let ctorInfo ← getConstInfoCtor ctorName
        let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
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
        alts := alts.push alt
      return alts

def mkFromJsonBodyForStruct (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let getters ← fields.mapM (fun field => do
    let getter ← `(getObjValAs? json _ $(Prod.snd <| ← mkJsonField field))
    let getter ← `(doElem| Except.mapError (fun s => (toString $(quote indName)) ++ "." ++ (toString $(quote field)) ++ ": " ++ s) <| $getter)
    return getter
  )
  let fields := fields.map mkIdent
  `(do
    $[let $fields:ident ← $getters]*
    return { $[$fields:ident := $(id fields)],* })

def mkFromJsonBodyForInduct (ctx : Context) (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let alts ← mkAlts indVal
  let auxTerm ← alts.foldrM (fun xs x => `(Except.orElseLazy $xs (fun _ => $x))) (← `(Except.error "no inductive constructor matched"))
  `($auxTerm)
where
  mkAlts (indVal : InductiveVal) : TermElabM (Array Term) := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← do forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut binders   := #[]
        let mut userNames := #[]
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)
        let fromJsonFuncId := mkIdent ctx.auxFunNames[0]!
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
          `((Json.parseTagged json $(quote ctorName.eraseMacroScopes.getString!) $(quote ctorInfo.numFields) $(quote userNamesOpt)).bind
            (fun jsons => do
              $[let $identNames:ident ← $fromJsons:doExpr]*
              return $(mkIdent ctorName):ident $identNames*))
        pure (stx, ctorInfo.numFields)
      alts := alts.push alt
  -- the smaller cases, especially the ones without fields are likely faster
  let alts' := alts.qsort (fun (_, x) (_, y) => x < y)
  return alts'.map Prod.fst

def mkToJsonBody (ctx : Context) (header : Header) (e : Expr): TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    mkToJsonBodyForStruct header indName
  else
    mkToJsonBodyForInduct ctx header indName

def mkToJsonAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let header     ←  mkToJsonHeader ctx.typeInfos[i]!
  let binders    := header.binders
  Term.elabBinders binders fun _ => do
  let type       ← Term.elabTerm header.targetType none
  let mut body   ← mkToJsonBody ctx header type
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx ``ToJson header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Json := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Json := $body:term)

def mkFromJsonBody (ctx : Context) (e : Expr) : TermElabM Term := do
  let indName := e.getAppFn.constName!
  if isStructure (← getEnv) indName then
    mkFromJsonBodyForStruct indName
  else
    mkFromJsonBodyForInduct ctx indName

def mkFromJsonAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indval     := ctx.typeInfos[i]!
  let header     ←  mkFromJsonHeader indval --TODO fix header info
  let binders    := header.binders
  Term.elabBinders binders fun _ => do
  let type ← Term.elabTerm header.targetType none
  let mut body ← mkFromJsonBody ctx type
  if ctx.usePartial || indval.isRec then
    let letDecls ← mkLocalInstanceLetDecls ctx ``FromJson header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Except String $(← mkInductiveApp ctx.typeInfos[i]! header.argNames) := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Except String $(← mkInductiveApp ctx.typeInfos[i]! header.argNames) := $body:term)


def mkToJsonMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkToJsonAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

def mkFromJsonMutualBlock (ctx : Context) : TermElabM Command := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkFromJsonAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkToJsonInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "toJson" declName
  let cmds := #[← mkToJsonMutualBlock ctx] ++ (← mkInstanceCmds ctx ``ToJson #[declName])
  trace[Elab.Deriving.toJson] "\n{cmds}"
  return cmds

private def mkFromJsonInstance (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext "fromJson" declName
  let cmds := #[← mkFromJsonMutualBlock ctx] ++ (← mkInstanceCmds ctx ``FromJson #[declName])
  trace[Elab.Deriving.fromJson] "\n{cmds}"
  return cmds

def mkToJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkToJsonInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

def mkFromJsonInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkFromJsonInstance declName
      cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``ToJson mkToJsonInstanceHandler
  registerDerivingHandler ``FromJson mkFromJsonInstanceHandler

  registerTraceClass `Elab.Deriving.toJson
  registerTraceClass `Elab.Deriving.fromJson

end Lean.Elab.Deriving.FromToJson
