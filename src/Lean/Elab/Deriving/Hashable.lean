/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
prelude
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.Hashable
open Command
open Lean.Parser.Term
open Meta

def mkHashableHeader (argNames : Array Name) (nestedOcc : NestedOccurence) : TermElabM Header := do
  mkHeader `Hashable 1 argNames nestedOcc

def mkMatch (ctx : Context) (header : Header) (e : Expr) (fvars : Array Expr) : TermElabM Term := do
  let f := e.getAppFn
  let ind := f.constName!
  let lvls := f.constLevels!
  let indVal ← getConstInfoInduct ind
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal lvls
  `(match $[$discrs],* with $alts:matchAlt*)
where

  mkAlts (indVal : InductiveVal) (lvl : List Level) : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    let mut ctorIdx := 0
    for ctorName in indVal.ctors do
      let args := e.getAppArgs
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorApp := mkAppN (mkConst ctorInfo.name lvl) args[:ctorInfo.numParams]
      let ctorType ← inferType ctorApp
      let alt ← forallTelescopeReducing ctorType fun xs _ => do
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhs ← `($(quote ctorIdx))
        -- add `_` for inductive parameters, they are inaccessible
        for _ in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let x := xs[i]!
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          let xType ← inferType x
          if let some auxFunName ← ctx.getFunName? header xType fvars then
            rhs ← `(mixHash $rhs ($(mkIdent auxFunName) $a))
          else
            rhs ← `(mixHash $rhs (hash $a:ident))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
      ctorIdx := ctorIdx + 1
    return alts

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let nestedOcc  := ctx.typeInfos[i]!
  let argNames   := ctx.typeArgNames[i]!
  let header     ←  mkHashableHeader argNames nestedOcc
  let binders    := header.binders
  Term.elabBinders binders fun xs => do
  let type ← Term.elabTerm header.targetType none
  let mut body       ←  mkMatch ctx header type xs
  if ctx.usePartial then
    -- TODO(Dany): Get rid of this code branch altogether once we have well-founded recursion
    let letDecls ← mkLocalInstanceLetDecls ctx `Hashable header.argNames
    body ← mkLet letDecls body
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : UInt64 := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : UInt64 := $body:term)

def mkHashFuncs (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

private def mkHashableInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "hash" declName false
  let cmds := #[← mkHashFuncs ctx] ++ (← mkInstanceCmds ctx `Hashable)
  trace[Elab.Deriving.hashable] "\n{cmds}"
  return cmds

def mkHashableHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive)  then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkHashableInstanceCmds declName
      cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``Hashable mkHashableHandler
  registerTraceClass `Elab.Deriving.hashable
