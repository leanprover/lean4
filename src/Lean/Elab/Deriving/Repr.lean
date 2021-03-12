/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.Repr
open Lean.Parser.Term
open Meta
open Std

def mkReprHeader (ctx : Context) (indVal : InductiveVal) : TermElabM Header := do
  let prec ← `(prec)
  let header ← mkHeader ctx `Repr 1 indVal
  return { header with
    binders := header.binders.push (← `(explicitBinderF| (prec : Nat)))
  }

def mkBodyForStruct (ctx : Context) (header : Header) (indVal : InductiveVal) : TermElabM Syntax := do
  let ctorVal ← getConstInfoCtor indVal.ctors.head!
  let fieldNames ← getStructureFields (← getEnv) indVal.name
  let numParams := indVal.numParams
  let target    := mkIdent header.targetNames[0]
  forallTelescopeReducing ctorVal.type fun xs _ => do
    let mut fields : Syntax ← `(Format.nil)
    let mut first := true
    if xs.size != numParams + fieldNames.size then
      throwError "'deriving Repr' failed, unexpected number of fields in structure"
    for i in [:fieldNames.size] do
      let fieldName := fieldNames[i]
      let fieldNameLit := Syntax.mkStrLit (toString fieldName)
      let x := xs[numParams + i]
      if first then
        first := false
      else
        fields ← `($fields ++ "," ++ Format.line)
      if (← isType x <||> isProof x) then
        fields ← `($fields ++ $fieldNameLit ++ " := " ++ "_")
      else
        fields ← `($fields ++ $fieldNameLit ++ " := " ++ repr ($target.$(mkIdent fieldName):ident))
    `(Format.bracket "{ " $fields:term " }")

def mkBodyForInduct (ctx : Context) (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Syntax := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array Syntax) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for i in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhs := Syntax.mkStrLit (toString ctorInfo.name)
        rhs ← `(Format.text $rhs)
        -- add `_` for inductive parameters, they are inaccessible
        for i in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          if (← inferType x).isAppOf indVal.name then
            rhs ← `($rhs ++ Format.line ++ $(mkIdent auxFunName):ident $a:ident max_prec)
          else
            rhs ← `($rhs ++ Format.line ++ reprArg $a)
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        `(matchAltExpr| | $[$patterns:term],* => Repr.addAppParen (Format.group (Format.nest (if prec >= max_prec then 1 else 2) ($rhs:term))) prec)
      alts := alts.push alt
    return alts

def mkBody (ctx : Context) (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Syntax := do
  if isStructure (← getEnv) indVal.name then
    mkBodyForStruct ctx header indVal
  else
    mkBodyForInduct ctx header indVal auxFunName

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Syntax := do
  let auxFunName ← ctx.auxFunNames[i]
  let indVal     ← ctx.typeInfos[i]
  let header     ← mkReprHeader ctx indVal
  let mut body   ← mkBody ctx header indVal auxFunName
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx `Repr header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    `(private partial def $(mkIdent auxFunName):ident $binders:explicitBinder* : Format := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:explicitBinder* : Format := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkReprInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "repr" declNames[0]
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `Repr declNames)
  trace[Elab.Deriving.repr] "\n{cmds}"
  return cmds

open Command

def mkReprInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM none <| mkReprInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerBuiltinDerivingHandler `Repr mkReprInstanceHandler
  registerTraceClass `Elab.Deriving.repr

end Lean.Elab.Deriving.Repr
