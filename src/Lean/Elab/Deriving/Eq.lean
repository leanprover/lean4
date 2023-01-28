/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner
-/
import Lean.Meta.Transform
import Lean.Meta.Inductive
import Lean.Elab.Deriving.Basic

namespace Lean.Elab.Deriving.Eq
open Lean.Parser.Term
open Meta

structure SameCtorResult where
  beqArm : TSyntax ``matchAlt
  beqIffEqArm : TSyntax ``matchAlt

def hasFwdDeps (i : Nat) (xs : Array Expr) : MetaM Bool := do
  let x := xs[i]!
  for j in [i+1:xs.size] do
    let y := xs[j]!
    if ← isProof y then continue
    if (← inferType y).containsFVar x.fvarId! then
      return true
  return false

def sameCtorArm (indVal : InductiveVal) (ctorInfo : ConstructorVal)
    (beqFn beqIffEqFn : Syntax.Ident) : TermElabM SameCtorResult := do
  forallTelescopeReducing ctorInfo.type fun xs type => do
  let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
  let mut beq ← `(true)
  let mut proof ← `(⟨fun _ => rfl, fun _ => rfl⟩)
  let mut ctorArgs1 : List Term := []
  let mut ctorArgs2 : List Term := []
  for i in [:ctorInfo.numFields].toArray.reverse do
    let i := indVal.numParams + i
    let x := xs[i]!
    if type.containsFVar x.fvarId! then
      -- If resulting type depends on this field, we don't need to compare
      ctorArgs1 := (← `(_)) :: ctorArgs1
      ctorArgs2 := (← `(_)) :: ctorArgs2
      continue
    let a := mkIdent (← mkFreshUserName `x)
    let b := mkIdent (← mkFreshUserName `y)
    ctorArgs1 := a :: ctorArgs1
    ctorArgs2 := b :: ctorArgs2
    if (← inferType (← inferType x)).isProp then
      -- proofs are defeq
      continue
    let (beqTerm, spec) ←
      if (← inferType x).isAppOf indVal.name then
        beq ← `($beqFn $a $b && $beq)
        pure (← `($beqFn $a $b), ← `($beqIffEqFn $a $b))
      else if ← hasFwdDeps i xs then
        beq ← `(
          if h : $a == $b then
            have := $(quote i)
            have heq : $a = $b := (beq_iff_eq' $a $b).1 h
            by subst heq; exact $beq
          else
            false)
        pure (← `($a == $b), ← `(beq_iff_eq' $a $b))
      else
        beq ← `($a == $b && $beq)
        pure (← `($a == $b), ← `(beq_iff_eq' $a $b))
    proof ← withFreshMacroScope `(
      if h : $beqTerm then
        have heq : $a = $b := ($spec).1 h
        by subst heq; simp only [Bool.true_and, dif_pos, h]; first | done | exact $proof
      else
        have : $a ≠ $b := h ∘ ($spec).2
        ⟨by simp only [*, dif_neg, Bool.false_and, false_implies], (by injection ·; contradiction)⟩)
  -- add `_` for inductive parameters, they are inaccessible
  ctorArgs1 := .replicate indVal.numParams (← `(_)) ++ ctorArgs1
  ctorArgs2 := .replicate indVal.numParams (← `(_)) ++ ctorArgs2
  let patterns :=
    -- add `_` pattern for indices
    mkArray indVal.numIndices (← `(_)) ++
    #[← `(@$(mkCIdent ctorInfo.name) $(ctorArgs1.toArray)*),
      ← `(@$(mkCIdent ctorInfo.name) $(ctorArgs2.toArray)*)]
  return {
    beqArm := ← `(matchAltExpr| | $patterns,* => $beq)
    beqIffEqArm := ← `(matchAltExpr| | $patterns,* =>
      by simp only [$beqFn:ident]; first | done | exact $proof)
  }

def mkEqFuns (indVal : InductiveVal) (beqFn beqIffEqFn : Syntax.Ident)
    (params indices : Array Syntax.Ident) :
    TermElabM (Command × Command) := do
  let ctors ← indVal.ctors.mapM fun ctorName => do
    sameCtorArm indVal (← getConstInfoCtor ctorName) beqFn beqIffEqFn
  let indPatterns := mkArray indVal.numIndices (← `(_)) -- add `_` pattern for indices
  let beqArms := ctors.map (·.beqArm) ++ -- TODO: simplify after #2065
    [(← `(matchAltExpr| | $[$(indPatterns ++ #[← `(_), ← `(_)])],* => false) : TSyntax ``matchAlt)]
  let beqCmd ← `(
    set_option match.ignoreUnusedAlts true
    def $beqFn {$indices*} (lhs rhs : @$(mkCIdent indVal.name) $params* $indices*) : Bool :=
      -- TODO: simplify after #2065
      match $((← indices.mapM (`(matchDiscr| $(·):ident))) ++ #[← `(matchDiscr| lhs), ← `(matchDiscr| rhs)]):matchDiscr,* with
      $(beqArms.toArray):matchAlt*
  )
  let mut proofArms : Array (TSyntax ``matchAlt) := ctors.map (·.beqIffEqArm) |>.toArray
  for ctor1 in indVal.ctors do for ctor2 in indVal.ctors do
    if ctor1 = ctor2 then continue
    unless ← compatibleCtors ctor1 ctor2 do continue
    proofArms := proofArms.push <| ← `(matchAltExpr|
      -- TODO: simplify after #2065
      | $[$(indPatterns ++ #[← `(@$(mkCIdent ctor1) ..), ← `($(mkCIdent ctor2) ..)])],* =>
        ⟨(nomatch ·), (nomatch ·)⟩)
  let beqIffEqCmd ← `(
    theorem $beqIffEqFn {$indices*} (lhs rhs : @$(mkCIdent indVal.name) $params* $indices*) : $beqFn lhs rhs ↔ lhs = rhs :=
      -- TODO: simplify after #2065
      match $((← indices.mapM (`(matchDiscr| $(·):ident))) ++ #[← `(matchDiscr| lhs), ← `(matchDiscr| rhs)]):matchDiscr,* with
      $proofArms:matchAlt*
  )
  return (beqCmd, beqIffEqCmd)

def paramsWithFwdDeps (indVal : InductiveVal) : MetaM (HashSet Nat) := do
  let mut ps := {}
  for ctor in indVal.ctors do
    ps ← forallTelescopeReducing (← getConstInfoCtor ctor).type fun xs _ => do
      let mut ps := ps
      for i in [indVal.numParams:xs.size] do
        if ← hasFwdDeps i xs then
          let xsiType ← inferType xs[i]!
          for j in [:indVal.numParams], p in xs do
            if xsiType.containsFVar p.fvarId! then
              ps := ps.insert j
      return ps
  return ps

open Lean.Elab.Command
def mkInstancesDefault (indVal : InductiveVal) (decEq : Bool) : CommandElabM Unit := do
  elabCommand <| ← liftTermElabM do
    forallTelescopeReducing indVal.type fun paramsIndices _ => do
    let paramsIndicesIdents ← paramsIndices.mapM fun p =>
      return mkIdent (← mkFreshUserName (← p.fvarId!.getUserName).eraseMacroScopes)
    let params := paramsIndicesIdents[:indVal.numParams].toArray
    let indices := paramsIndicesIdents[indVal.numParams:].toArray
    let decEqParams ← paramsWithFwdDeps indVal
    let mut instsForBEq := #[]
    let mut instsForDecEq := #[]
    for i in [:indVal.numParams], p in paramsIndices, pn in params do
      if let .sort u ← whnfD (← inferType p) then
      if u.isEquiv .zero then continue
      instsForBEq := instsForBEq.push <| ←
        if decEqParams.contains i then
          `(bracketedBinderF| [DecidableEq $pn])
        else
          `(bracketedBinderF| [BEq $pn])
      instsForDecEq := instsForDecEq.push <| ← `(bracketedBinderF| [DecidableEq $pn])
    let beqFn : Ident ← `(beq_fn)
    let beqIffEqFn : Ident ← `(beq_iff_eq_fn)
    let (beqCmd, beqIffEqCmd) ← withFreshMacroScope do
      mkEqFuns indVal beqFn beqIffEqFn params indices
    let beqInst ← `(section
      variable $[{$params}]* $instsForBEq*
      $beqCmd:command
      instance {$indices*} : BEq (@$(mkCIdent indVal.name) $params* $indices*) where
        beq := $beqFn
      end)
    let decEqInst ← `(section
      variable $[{$params}]* $instsForDecEq*
      $beqIffEqCmd:command
      instance {$indices*} : DecidableEq (@$(mkCIdent indVal.name) $params* $indices*) where
        beq_iff_eq := $beqIffEqFn _ _
      end)
    if decEq then `($beqInst $decEqInst:command) else return beqInst

def mkInstanceHandler (decEq : Bool) (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size != 1 then
    return false -- mutually inductive types are not supported yet
  else if (← isEnumType declNames[0]!) then
    throwError "todo"
    -- mkDecEqEnum declNames[0]!
    return true
  else
    mkInstancesDefault (← getConstInfoInduct declNames[0]!) decEq
    return true

builtin_initialize
  registerDerivingHandler ``DecidableEq <| mkInstanceHandler (decEq := true)
  registerDerivingHandler ``BEq <| mkInstanceHandler (decEq := false)
