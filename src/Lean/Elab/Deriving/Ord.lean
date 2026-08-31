/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
module

prelude
public import Lean.Data.Options
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CasesOnSameCtor
import Lean.Meta.SameCtorUtils
import Init.Data.Array.OfFn

register_builtin_option deriving.ord.linear_construction_threshold : Nat := {
  defValue := 10
  descr := "If the inductive data type has this many or more constructors, use a different \
    implementation for implementing `Ord` that avoids the quadratic code size produced by the \
    default implementation.\n\n\
    The alternative construction compiles to less efficient code in some cases, so by default \
    it is only used for inductive types with 10 or more constructors." }

namespace Lean.Elab.Deriving.Ord
open Lean.Parser.Term
open Meta

def mkOrdHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `Ord 2 indVal

def mkMatchOld (header : Header) (indVal : InductiveVal) : TermElabM Term := do
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
        for _ in *...indVal.numIndices do
          indPatterns := indPatterns.push (← `(_))
        let mut ctorArgs1 := #[]
        let mut ctorArgs2 := #[]
        -- construct RHS top-down as continuation over the remaining comparison
        let mut rhsCont : Term → TermElabM Term := fun rhs => pure rhs
        -- add `_` for inductive parameters, they are inaccessible
        for _ in *...indVal.numParams do
          ctorArgs1 := ctorArgs1.push (← `(_))
          ctorArgs2 := ctorArgs2.push (← `(_))
        for i in *...ctorInfo.numFields do
          let x := xs[indVal.numParams + i]!
          if (← isProof x) then
            -- If resulting type depends on this field or is a proof, we don't need to compare
            ctorArgs1 := ctorArgs1.push (← `(_))
            ctorArgs2 := ctorArgs2.push (← `(_))
          else if occursOrInType (← getLCtx) x type then
            -- If resulting type depends on this field, we don't need to compare
            -- but use inaccessible patterns fail during pattern match compilation if their
            -- equality does not actually follow from the equality between their types
            let a := mkIdent (← mkFreshUserName `a)
            ctorArgs1 := ctorArgs1.push a
            ctorArgs2 := ctorArgs2.push (← `(term|.( $a:ident )))
          else
            let a := mkIdent (← mkFreshUserName `a)
            let b := mkIdent (← mkFreshUserName `b)
            ctorArgs1 := ctorArgs1.push a
            ctorArgs2 := ctorArgs2.push b
            rhsCont := fun rhs => `(Ordering.then (compare $a $b) $rhs) >>= rhsCont
        let lPat ← `(@$(mkIdent ctorName):ident $ctorArgs1:term*)
        let rPat ← `(@$(mkIdent ctorName):ident $ctorArgs2:term*)
        let patterns := indPatterns ++ #[lPat, rPat]
        let ltPatterns := indPatterns ++ #[lPat, ←`(_)]
        let gtPatterns := indPatterns ++ #[←`(_), lPat] -- Use the lPat again, we don’t want the `.(a)` pattern here
        let rhs ← rhsCont (← `(Ordering.eq))
        pure #[←`(matchAltExpr| | $[$(patterns):term],* => $rhs:term),
               ←`(matchAltExpr| | $[$(ltPatterns):term],* => Ordering.lt),
               ←`(matchAltExpr| | $[$(gtPatterns):term],* => Ordering.gt)]
      alts := alts ++ (alt : Array (TSyntax ``matchAlt))
    return alts.pop.pop

def mkMatchNew (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  assert! header.targetNames.size == 2

  let x1 := mkIdent header.targetNames[0]!
  let x2 := mkIdent header.targetNames[1]!
  let ctorIdxName := mkCtorIdxName indVal.name
  -- NB: the getMatcherInfo? assumes all matchers are called `match_`
  let casesOnSameCtorName ← mkFreshUserName (indVal.name ++ `match_on_same_ctor)
  mkCasesOnSameCtor casesOnSameCtorName indVal.name
  let alts ← Array.ofFnM (n := indVal.numCtors) fun ⟨ctorIdx, _⟩ => do
    let ctorName := indVal.ctors[ctorIdx]!
    let ctorInfo ← getConstInfoCtor ctorName
    forallTelescopeReducing ctorInfo.type fun xs type => do
      let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
      let mut ctorArgs1 : Array Term := #[]
      let mut ctorArgs2 : Array Term := #[]

      let mut rhsCont : Term → TermElabM Term := fun rhs => pure rhs
      for i in *...ctorInfo.numFields do
        let x := xs[indVal.numParams + i]!
        if occursOrInType (← getLCtx) x type then
          -- If resulting type depends on this field, we don't need to compare
          -- and the casesOnSameCtor only has a parameter for it once
          ctorArgs1 := ctorArgs1.push (← `(_))
        else
          let userName ← x.fvarId!.getUserName
          let a := mkIdent (← mkFreshUserName userName)
          let b := mkIdent (← mkFreshUserName (userName.appendAfter "'"))
          ctorArgs1 := ctorArgs1.push a
          ctorArgs2 := ctorArgs2.push b
          let xType ← inferType x
          if (← isProp xType) then
            continue
          else
            rhsCont := fun rhs => `(Ordering.then (compare $a $b) $rhs) >>= rhsCont
      let rhs ← rhsCont (← `(Ordering.eq))
      if ctorArgs1.isEmpty then
        -- Unit thunking argument
        ctorArgs1 := ctorArgs1.push (← `(()))
      `(@fun $ctorArgs1:term* $ctorArgs2:term* =>$rhs:term)
  if indVal.numCtors == 1 then
    `( $(mkCIdent casesOnSameCtorName) $x1:term $x2:term rfl $alts:term* )
  else
    `( match h : compare ($(mkCIdent ctorIdxName) $x1:ident) ($(mkCIdent ctorIdxName) $x2:ident) with
      | Ordering.lt => Ordering.lt
      | Ordering.gt => Ordering.gt
      | Ordering.eq =>
        $(mkCIdent casesOnSameCtorName) $x1:term $x2:term (Nat.compare_eq_eq.mp h) $alts:term*
     )

def mkMatch (header : Header) (indVal : InductiveVal) : TermElabM Term := do
  if indVal.numCtors ≥ deriving.ord.linear_construction_threshold.get (← getOptions) then
    mkMatchNew header indVal
  else
    mkMatchOld header indVal

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkOrdHeader indVal
  let mut body   ← mkMatch header indVal
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx `Ord header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Ordering := $body:term)
  else
    `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Ordering := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in *...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     set_option match.ignoreUnusedAlts true
     $auxDefs:command*
    end)

private def mkOrdInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Ord "ord" declName (supportsRec := false)
  let mut cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `Ord #[declName])
  unless ctx.usePartial do
    cmds := cmds.push (← `(command| attribute [method_specs] $(mkIdent ctx.instName):ident))
  trace[Elab.Deriving.ord] "\n{cmds}"
  return cmds

private def mkOrdEnumFun (ctx : Context) (name : Name) : TermElabM Syntax := do
  let auxFunName := ctx.auxFunNames[0]!
  `(def $(mkIdent auxFunName):ident (x y : $(mkCIdent name)) : Ordering := compare x.ctorIdx y.ctorIdx)

private def mkOrdEnumCmd (name : Name): TermElabM (Array Syntax) := do
  let ctx ← mkContext ``Ord "ord" name
  let cmds := #[← mkOrdEnumFun ctx name] ++ (← mkInstanceCmds ctx `Ord #[name])
  trace[Elab.Deriving.ord] "\n{cmds}"
  return cmds

open Command

def mkOrdInstance (declName : Name) : CommandElabM Unit := do
  withoutExposeFromCtors declName do
    let cmds ← liftTermElabM <|
      if (← isEnumType declName) then
        mkOrdEnumCmd declName
      else
        mkOrdInstanceCmds declName
    cmds.forM elabCommand

def mkOrdInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      mkOrdInstance declName
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `Ord mkOrdInstanceHandler
  registerTraceClass `Elab.Deriving.ord

end Lean.Elab.Deriving.Ord
