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

private def parseTagged 
    (json : Json) 
    (tag : String) 
    (nFields : Nat) 
    (fieldNames? : Option (Array Name)) : Except String (Array Json) :=
  if nFields == 0 then
    match getStr? json with
    | Except.ok s => if s == tag then Except.ok #[] else throw s!"incorrect tag: {s} ≟ {tag}"
    | Except.error err => Except.error err
  else
    match getObjVal? json tag with
    | Except.ok payload => 
      match fieldNames? with
      | some fieldNames => 
        do
          let mut fields := #[]
          for fieldName in fieldNames do
            fields := fields.push (←getObjVal? payload fieldName.getString!)
          Except.ok fields
      | none => 
        if nFields == 1 then 
          Except.ok #[payload]
        else
          match getArr? payload with
          | Except.ok fields => 
            if fields.size == nFields then 
              Except.ok fields 
            else 
              Except.error "incorrect number of fields: {fields.size} ≟ {nFields}"
          | Except.error err => Except.error err
    | Except.error err => Except.error err

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
        let header ← mkHeader ctx ``ToJson 1 ctx.typeInfos[0]
        let discrs ← mkDiscrs header indVal
        let alts ← mkAlts indVal fun ctor args userNames =>
          match args, userNames with
          | #[], _ => `(toJson $(quote ctor.name.getString!))
          | #[x], none => `(mkObj [($(quote ctor.name.getString!), toJson $x)])
          | xs, none => do
            let xs ← xs.mapM fun x => `(toJson $x)
            `(mkObj [($(quote ctor.name.getString!), toJson #[$[$xs:term],*])])
          | xs, some userNames => do
            let xs ← xs.mapIdxM fun idx x => `(($(quote userNames[idx].getString!), toJson $x))
            `(mkObj [($(quote ctor.name.getString!), mkObj [$[$xs:term],*])])
        let auxCmd ← `(match $[$discrs],* with $alts:matchAlt*)
        let auxCmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* := $auxCmd)
        return #[auxCmd] ++ (← mkInstanceCmds ctx ``ToJson declNames)
      cmds.forM elabCommand
      return true
  else
    return false
where
  mkAlts 
    (indVal : InductiveVal) 
    (rhs : ConstructorVal → Array Syntax → (Option $ Array Name) → TermElabM Syntax) : TermElabM (Array Syntax) := do
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
      let mut identNames := #[]
      let mut userNames := #[]
      for i in [:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]
        let localDecl ← getLocalDecl x.fvarId!
        if !localDecl.userName.hasMacroScopes then
          userNames := userNames.push localDecl.userName
        let a := mkIdent (← mkFreshUserName `a)
        identNames := identNames.push a
        ctorArgs := ctorArgs.push a
      patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
      let rhs ← rhs ctorInfo identNames (if userNames.size == identNames.size then some userNames else none)
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
        let discrs ← mkDiscrs header indVal
        let alts ← mkAlts indVal 
        let matchCmd ← alts.foldrM (fun xs x => `($xs <|> $x)) (←`(Except.error "no inductive constructor matched"))
        let cmd ← `(private def $(mkIdent ctx.auxFunNames[0]):ident $header.binders:explicitBinder* (json : Json)
          : Except String $(← mkInductiveApp ctx.typeInfos[0] header.argNames) :=
            $matchCmd )
        return #[cmd] ++ (← mkInstanceCmds ctx ``FromJson declNames)
      cmds.forM elabCommand
      return true
  else
    return false
where
  mkAlts (indVal : InductiveVal) : TermElabM (Array Syntax) := do
  let alts ← 
    indVal.ctors.toArray.mapM fun ctor => do
      let ctorInfo ← getConstInfoCtor ctor
      forallTelescopeReducing ctorInfo.type fun xs type => do
        let mut identNames := #[]
        let mut userNames := #[]
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]
          let localDecl ← getLocalDecl x.fvarId!
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          identNames := identNames.push a
        let jsonAccess ← identNames.mapIdxM (fun idx _ => `(jsons[$(quote idx.val)]))
        let userNamesOpt ← 
          if identNames.size == userNames.size then 
            `(some #[$[$(userNames.map quote):ident],*])
          else `(none)
        let stx ← 
          `((parseTagged json $(quote ctor.getString!) $(quote ctorInfo.numFields) $(quote userNamesOpt)).bind 
            (fun jsons => do
            $[let $identNames:ident ← fromJson? $jsonAccess]*
            return $(mkIdent ctor):ident $identNames*))
        (stx, ctorInfo.numFields)
  -- the smaller cases, especially the ones without fields are likely faster
  let alts := alts.qsort (fun (_, x) (_, y) => x < y)
  alts.map Prod.fst
  
builtin_initialize
  registerBuiltinDerivingHandler ``ToJson mkToJsonInstanceHandler
  registerBuiltinDerivingHandler ``FromJson mkFromJsonInstanceHandler

end Lean.Elab.Deriving.FromToJson
