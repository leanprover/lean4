/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.Ord
open Lean.Parser.Term
open Meta

def mkOrdHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `Ord 2 indVal

def mkMatch (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
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
          let x := xs[indVal.numParams + i]!
          if type.containsFVar x.fvarId! || (←isProp (←inferType x)) then
            -- If resulting type depends on this field or is a proof, we don't need to compare
            ctorArgs1 := ctorArgs1.push (← `(_))
            ctorArgs2 := ctorArgs2.push (← `(_))
          else
            let a := mkIdent (← mkFreshUserName `a)
            let b := mkIdent (← mkFreshUserName `b)
            ctorArgs1 := ctorArgs1.push a
            ctorArgs2 := ctorArgs2.push b
            rhsCont := fun rhs => `(match compare $a $b with
              | Ordering.lt => Ordering.lt
              | Ordering.gt => Ordering.gt
              | Ordering.eq => $rhs) >>= rhsCont
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
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkOrdHeader indVal
  let mut body   ← mkMatch header indVal
  if ctx.usePartial || indVal.isRec then
    let letDecls ← mkLocalInstanceLetDecls ctx `Ord header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial || indVal.isRec then
    `(private partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Ordering := $body:term)
  else
    `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Ordering := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     $auxDefs:command*
    end)

private def mkOrdInstanceCmds (declNames : Array Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "ord" declNames[0]!
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `Ord declNames)
  trace[Elab.Deriving.ord] "\n{cmds}"
  return cmds

open Command

def mkOrdInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) && declNames.size > 0 then
    let cmds ← liftTermElabM <| mkOrdInstanceCmds declNames
    cmds.forM elabCommand
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `Ord mkOrdInstanceHandler
  registerTraceClass `Elab.Deriving.ord

end Lean.Elab.Deriving.Ord
