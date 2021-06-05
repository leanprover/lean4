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

def mkHashableHeader (ctx : Context) (indVal : InductiveVal) : TermElabM Header := do
  mkHeader ctx `Hashable 1 indVal

def mkMatch (ctx : Context) (header : Header) (indVal : InductiveVal) (auxFuncIdx : Nat) : TermElabM Syntax := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where

  mkAlts : TermElabM (Array Syntax) := do
    let mut alts := #[]
    let mut ctorIdx := 0
    let allIndVals := indVal.all.toArray
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
        let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
        let mut patterns := #[]
        -- add `_` pattern for indices
        for i in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        let mut rhs ← `($(quote ctorIdx))
        -- add `_` for inductive parameters, they are inaccessible
        for i in [:indVal.numParams] do
          ctorArgs := ctorArgs.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let x := xs[indVal.numParams + i]
          let xTy ← inferType x
          let typeName := xTy.getAppFn.constName!
          let a := mkIdent (← mkFreshUserName `a)
          ctorArgs := ctorArgs.push a
          match allIndVals.findIdx? (· == typeName) with
          | some x => rhs ← `(mixHash $rhs ($(mkIdent ctx.auxFunNames[x]) $a:ident))
          | none => rhs ← `(mixHash $rhs (hash $a:ident))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs:term*))
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
      ctorIdx := ctorIdx + 1
    return alts

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Syntax := do
  let auxFunName ← ctx.auxFunNames[i]
  let indVal     ← ctx.typeInfos[i]
  let header     ← mkHashableHeader ctx indVal
  let body       ← mkMatch ctx header indVal i
  let binders    := header.binders
  if ctx.usePartial then
    -- TODO(Dany): Get rid of this code branch altogether once we have well-founded recursion
    `(private partial def $(mkIdent auxFunName):ident $binders:explicitBinder* : UInt64 := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:explicitBinder* : UInt64 := $body:term)

def mkHashFuncs (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual $auxDefs:command* end)

private def mkHashableInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "hash" declNames[0]
  let cmds := #[← mkHashFuncs ctx] ++ (← mkInstanceCmds ctx `Hashable declNames)
  trace[Elab.Deriving.hashable] "\n{cmds}"
  return cmds

def mkHashableHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM none <| mkHashableInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerBuiltinDerivingHandler ``Hashable mkHashableHandler
  registerTraceClass `Elab.Deriving.hashable