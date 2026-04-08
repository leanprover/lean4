/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
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

namespace Lean.Elab.Deriving.BEq
open Lean.Parser.Term
open Meta


register_builtin_option deriving.beq.linear_construction_threshold : Nat := {
  defValue := 10
  descr := "If the inductive data type has this many or more constructors, use a different \
    implementation for implementing `BEq` that avoids the quadratic code size produced by the \
    default implementation.\n\n\
    The alternative construction compiles to less efficient code in some cases, so by default \
    it is only used for inductive types with 10 or more constructors." }

def mkBEqHeader (indVal : InductiveVal) : TermElabM Header := do
  mkHeader `BEq 2 indVal

def mkMatchOld (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkElseAlt : TermElabM (TSyntax ``matchAltExpr) := do
    let mut patterns := #[]
    -- add `_` pattern for indices
    for _ in *...indVal.numIndices do
      patterns := patterns.push (← `(_))
    patterns := patterns.push (← `(_))
    patterns := patterns.push (← `(_))
    let altRhs ← `(false)
    `(matchAltExpr| | $[$patterns:term],* => $altRhs:term)

  mkAlts : TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs type => do
        let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in *...indVal.numIndices do
          patterns := patterns.push (← `(_))
        let mut ctorArgs1 : Array Term := #[]
        let mut ctorArgs2 : Array Term := #[]
        let mut rhs ← `(true)
        let mut rhs_empty := true
        for i in *...ctorInfo.numFields do
          let pos := indVal.numParams + ctorInfo.numFields - i - 1
          let x := xs[pos]!
          if occursOrInType (← getLCtx) x type then
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
            let xType ← inferType x
            if (← isProp xType) then
              continue
            if xType.isAppOf indVal.name then
              if rhs_empty then
                rhs ← `($(mkIdent auxFunName):ident $a:ident $b:ident)
                rhs_empty := false
              else
                rhs ← `($(mkIdent auxFunName):ident $a:ident $b:ident && $rhs)
            /- If `x` appears in the type of another field, use `eq_of_beq` to
               unify the types of the subsequent variables -/
            else if ← xs[(pos+1)...*].anyM
                (fun fvar => (Expr.containsFVar · x.fvarId!) <$> (inferType fvar)) then
              rhs ← `(if h : $a:ident == $b:ident then by
                        cases (eq_of_beq h)
                        exact $rhs
                      else false)
              rhs_empty := false
            else
              if rhs_empty then
                rhs ← `($a:ident == $b:ident)
                rhs_empty := false
              else
                rhs ← `($a:ident == $b:ident && $rhs)
          -- add `_` for inductive parameters, they are inaccessible
        for _ in *...indVal.numParams do
          ctorArgs1 := ctorArgs1.push (← `(_))
          ctorArgs2 := ctorArgs2.push (← `(_))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs1.reverse:term*))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs2.reverse:term*))
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
    alts := alts.push (← mkElseAlt)
    return alts

def mkMatchNew (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Term := do
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

      let mut rhs ← `(true)
      let mut rhs_empty := true
      for i in *...ctorInfo.numFields do
        let pos := indVal.numParams + ctorInfo.numFields - i - 1
        let x := xs[pos]!
        if type.containsFVar x.fvarId! then
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
          if xType.isAppOf indVal.name then
            if rhs_empty then
              rhs ← `($(mkIdent auxFunName):ident $a:ident $b:ident)
              rhs_empty := false
            else
              rhs ← `($(mkIdent auxFunName):ident $a:ident $b:ident && $rhs)
          /- If `x` appears in the type of another field, use `eq_of_beq` to
              unify the types of the subsequent variables -/
          else if ← xs[(pos+1)...*].anyM
              (fun fvar => (Expr.containsFVar · x.fvarId!) <$> (inferType fvar)) then
            rhs ← `(if h : $a:ident == $b:ident then by
                      cases (eq_of_beq h)
                      exact $rhs
                    else false)
            rhs_empty := false
          else
            if rhs_empty then
              rhs ← `($a:ident == $b:ident)
              rhs_empty := false
            else
              rhs ← `($a:ident == $b:ident && $rhs)
      if ctorArgs1.isEmpty then
        -- Unit thunking argument
        ctorArgs1 := ctorArgs1.push (← `(()))
      `(@fun $ctorArgs1.reverse:term* $ctorArgs2.reverse:term* =>$rhs:term)
  if indVal.numCtors == 1 then
    `( $(mkCIdent casesOnSameCtorName) $x1:term $x2:term rfl $alts:term* )
  else
    `( match decEq ($(mkCIdent ctorIdxName) $x1:ident) ($(mkCIdent ctorIdxName) $x2:ident) with
      | .isTrue h => $(mkCIdent casesOnSameCtorName) $x1:term $x2:term h $alts:term*
      | .isFalse _ => false)

def mkMatch (header : Header) (indVal : InductiveVal) (auxFunName : Name) : TermElabM Term := do
  if indVal.numCtors ≥ deriving.beq.linear_construction_threshold.get (← getOptions) then
    mkMatchNew header indVal auxFunName
  else
    mkMatchOld header indVal auxFunName


def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let indVal     := ctx.typeInfos[i]!
  let header     ← mkBEqHeader indVal
  let mut body   ← mkMatch header indVal auxFunName
  if ctx.usePartial then
    let letDecls ← mkLocalInstanceLetDecls ctx `BEq header.argNames
    body ← mkLet letDecls body
  let binders    := header.binders
  if ctx.usePartial then
    `(partial def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Bool := $body:term)
  else
    `(def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Bool := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in *...ctx.typeInfos.size do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     set_option match.ignoreUnusedAlts true
     $auxDefs:command*
    end)

def mkBEqInstanceCmds (ctx : Context) (declName : Name) : TermElabM (Array Syntax) := do
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `BEq #[declName])
  trace[Elab.Deriving.beq] "\n{cmds}"
  return cmds

def mkBEqEnumFun (ctx : Context) (name : Name) : TermElabM Syntax := do
  let auxFunName := ctx.auxFunNames[0]!
  `(def $(mkIdent auxFunName):ident  (x y : $(mkCIdent name)) : Bool := x.ctorIdx == y.ctorIdx)

def mkBEqEnumCmd (ctx : Context) (name : Name): TermElabM (Array Syntax) := do
  let cmds := #[← mkBEqEnumFun ctx name] ++ (← mkInstanceCmds ctx `BEq #[name])
  trace[Elab.Deriving.beq] "\n{cmds}"
  return cmds

open Command

def mkBEqInstance (declName : Name) : CommandElabM Unit := do
  withoutExposeFromCtors declName do
    let ctx ← liftTermElabM <| mkContext ``BEq "beq" declName
    let cmds ← liftTermElabM <|
      if (← isEnumType declName) then
        mkBEqEnumCmd ctx declName
      else
        mkBEqInstanceCmds ctx declName
    cmds.forM elabCommand
    unless ctx.usePartial do
      elabCommand (← `(attribute [method_specs] $(mkIdent ctx.instName):ident))

def mkBEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      mkBEqInstance declName
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `BEq mkBEqInstanceHandler
  registerTraceClass `Elab.Deriving.beq

end Lean.Elab.Deriving.BEq
