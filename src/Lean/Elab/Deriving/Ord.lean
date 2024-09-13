/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
prelude
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.Ord
open Lean.Parser.Term
open Meta

def mkOrdHeader (argNames : Array Name) (indTypeFormer : IndTypeFormer) : TermElabM Header := do
  mkHeader `Ord 2 argNames indTypeFormer

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
    for ctorName in indVal.ctors do
      let args := e.getAppArgs
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorApp := mkAppN (mkConst ctorInfo.name lvl) args[:ctorInfo.numParams]
      let ctorType ← inferType ctorApp
      let alt ← forallTelescopeReducing ctorType fun xs type => do
        let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
        let mut indPatterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          indPatterns := indPatterns.push (← `(_))
        let mut ctorArgs1 := #[]
        let mut ctorArgs2 := #[]
        -- construct RHS top-down as continuation over the remaining comparison
        let mut rhsCont : Term → TermElabM Term := fun rhs => pure rhs
        -- add `_` for inductive parameters, they are inaccessible
        for _ in [:indVal.numParams] do
          ctorArgs1 := ctorArgs1.push (← `(_))
          ctorArgs2 := ctorArgs2.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let x := xs[i]!
          let xType ← inferType x
          if type.containsFVar x.fvarId! || (←isProp xType) then
            -- If resulting type depends on this field or is a proof, we don't need to compare
            ctorArgs1 := ctorArgs1.push (← `(_))
            ctorArgs2 := ctorArgs2.push (← `(_))
          else
            let a := mkIdent (← mkFreshUserName `a)
            let b := mkIdent (← mkFreshUserName `b)
            ctorArgs1 := ctorArgs1.push a
            ctorArgs2 := ctorArgs2.push b
            let compare ←
              if let some auxFunName ← ctx.getFunName? header xType fvars then
                `($(mkIdent auxFunName) $a $b)
              else
                `(compare $a $b)
            rhsCont := fun rhs => `(Ordering.then $compare $rhs) >>= rhsCont
        let lPat ← `(@$(mkIdent ctorName):ident $ctorArgs1:term*)
        let rPat ← `(@$(mkIdent ctorName):ident $ctorArgs2:term*)
        let patterns := indPatterns ++ #[lPat, rPat]
        let ltPatterns := indPatterns ++ #[lPat, ←`(_)]
        let gtPatterns := indPatterns ++ #[←`(_), rPat]
        let rhs ← rhsCont (← `(Ordering.eq))
        pure #[←`(matchAltExpr| | $[$(patterns):term],* => $rhs:term),
               ←`(matchAltExpr| | $[$(ltPatterns):term],* => Ordering.lt),
               ←`(matchAltExpr| | $[$(gtPatterns):term],* => Ordering.gt)]
      alts := alts ++ (alt : Array (TSyntax ``matchAlt))
    return alts.pop.pop

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName    := ctx.auxFunNames[i]!
  let indTypeFormer := ctx.typeInfos[i]!
  let argNames      := ctx.typeArgNames[i]!
  let header        ← mkOrdHeader argNames indTypeFormer
  let binders       := header.binders
  Term.elabBinders binders fun xs => do
  let type ← Term.elabTerm header.targetType none
  let body ←  mkMatch ctx header type xs
  `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Ordering := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     set_option match.ignoreUnusedAlts true
     $auxDefs:command*
    end)

private def mkOrdInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "ord" declName
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `Ord)
  trace[Elab.Deriving.ord] "\n{cmds}"
  return cmds

open Command

def mkOrdInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      let cmds ← liftTermElabM <| mkOrdInstanceCmds declName
      cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `Ord mkOrdInstanceHandler
  registerTraceClass `Elab.Deriving.ord

end Lean.Elab.Deriving.Ord
