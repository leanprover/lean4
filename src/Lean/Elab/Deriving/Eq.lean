/-
Copyright (c) 2023 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner
-/
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic

theorem beq_iff_eq' [DecidableEq α] (a b : α) : a == b ↔ a = b := beq_iff_eq
theorem Eq.to_iff (h : p = q) : p ↔ q := h ▸ .rfl

def Std.Range.toArray (range : Range) : Array Nat := Id.run do
  let mut out := #[]
  for i in range do
    out := out.push i
  return out

namespace Lean.Elab.Deriving.Eq
open Lean.Parser.Term
open Meta

structure SameCtorResult where
  beqArm : TSyntax ``matchAlt
  beqIffEqArm : TSyntax ``matchAlt

def sameCtorArm (indVal : InductiveVal) (ctorInfo : ConstructorVal)
    (beqFn beqIffEqFn : Syntax.Ident) : TermElabM SameCtorResult := do
  forallTelescopeReducing ctorInfo.type fun xs type => do
  let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
  let mut beq ← `(true)
  let mut proof ← `(⟨fun _ => rfl, fun _ => rfl⟩)
  let mut ctorArgs1 := []
  let mut ctorArgs2 := []
  for i in [:ctorInfo.numFields].toArray.reverse do
    let a ← withFreshMacroScope `(a)
    let b ← withFreshMacroScope `(b)
    ctorArgs1 := a :: ctorArgs1
    ctorArgs2 := b :: ctorArgs1
    let x := xs[indVal.numParams + i]!
    if (← inferType (← inferType x)).isProp then
      -- proofs are defeq
      continue
    if type.containsFVar x.fvarId! then
      -- If resulting type depends on this field, we don't need to compare
      continue
    let (beqTerm, spec) ←
      if (← inferType x).isAppOf indVal.name then
        beq ← `($beqFn $a $b && $beq)
        pure (← `($beqFn $a $b), ← `($beqIffEqFn $a $b))
      else if true then -- TODO: only if forward deps
        beq ← `(
          if h : $a == $b then
            by subst (beq_iff_eq' $a $b).1 h; exact $beq
          else
            false)
        pure (← `($a == $b), ← `(beq_iff_eq' $a $b))
      else
        beq ← `($a == $b && $beq)
        pure (← `($a == $b), ← `(beq_iff_eq' $a $b))
    proof ← withFreshMacroScope `(
      match h : $beqTerm with
      | true =>
        have heq : $a = $b := ($spec).1 h
        by subst heq; exact $proof
      | false =>
        have hne : $a ≠ $b :=
          fun h' => nomatch h.symm.trans (($spec).2 h')
        ⟨(nomatch ·), (by injection ·; contradiction)⟩)
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
    beqIffEqArm := ← `(matchAltExpr| | $patterns,* => $proof)
  }

def mkHelperFuns (indVal : InductiveVal) (beqFn beqIffEqFn : Syntax.Ident)
    (params indices : Array Syntax.Ident) (decEq := true) :
    TermElabM SameCtorResult := do
  let ctors ← indVal.ctors.mapM fun ctorName => do
    sameCtorArm indVal (← getConstInfoCtor ctorName) beqFn beqIffEqFn
  let indPatterns := mkArray indVal.numIndices (← `(_)) -- add `_` pattern for indices
  let beqArms := ctors.map (·.beqArm) ++
    [(← `(matchAltExpr| | $indPatterns,*, _, _ => false) : TSyntax ``matchAlt)]
  let beqCmd ← `(
    def $beqFn (lhs rhs : @$(mkCIdent indVal.name) $params* $indices*) : Bool
      $(beqArms.toArray):matchAlt*
  )
  let mut proofArms : Array (TSyntax ``matchAlt) := ctors.map (·.beqIffEqArm) |>.toArray
  for ctor1 in indVal.ctors do for ctor2 in indVal.ctors do
    if ctor1 = ctor2 then continue
    proofArms := proofArms.push <| ← `(matchAltExpr|
      | $indPatterns,*, @$(mkCIdent ctor1) .., @$(mkCIdent ctor2) .. =>
        ⟨(nomatch ·), (nomatch ·)⟩)
  _
