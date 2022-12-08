/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.Hashable
open Command
open Lean.Parser.Term
open Meta

def mkHashableHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `Hashable 1 indVal

def mkMatch (ctx : Context) (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where

  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    let mut ctorIdx := 0
    let allIndVals := indVal.all.toArray
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
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
          let x := xs[indVal.numParams + i]!
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          let xTy ← whnf (← inferType x)
          match xTy.getAppFn with
          | .const declName .. =>
            match allIndVals.findIdx? (· == declName) with
            | some x => rhs ← `(mixHash $rhs ($(mkIdent ctx.auxFunNames[x]!) $a:ident))
            | none => rhs ← `(mixHash $rhs (hash $a:ident))
          | _ => rhs ← `(mixHash $rhs (hash $a:ident))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
      ctorIdx := ctorIdx + 1
    return alts

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkHashableHeader indVal
  let mut body   ← mkMatch ctx header indVal
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx `Hashable header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    -- TODO(Dany): Get rid of this code branch altogether once we have well-founded recursion
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : UInt64 := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : UInt64 := $body:term)

def mkHashFuncs (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

private def mkHashableInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "hash" declNames[0]!
  let cmds := #[← mkHashFuncs ctx] ++ (← mkInstanceCmds ctx `Hashable declNames)
  trace[Elab.Deriving.hashable] "\n{cmds}"
  return cmds

def mkHashableHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM <| mkHashableInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler ``Hashable mkHashableHandler
  registerTraceClass `Elab.Deriving.hashable
