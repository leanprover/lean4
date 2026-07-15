/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Lean.Meta.Tactic.BVDecide.Normalize.Basic

/-!
This module contains the implementation of the pre processing pass for reducing `UIntX`/`IntX` to
`BitVec` and thus allow `bv_decide` to reason about them.

It:
1. runs the `int_toBitVec` simp set
2. If `USize.toBitVec`/`ISize.toBitVec` is used anywhere looks for equations of the form
   `System.Platform.numBits = constant` (or flipped) and uses them to convert the system back to
   fixed width.
-/

namespace Lean.Meta.Tactic.BVDecide
namespace Normalize

/--
Contains information for the `USize`/`ISize` elimination pass.
-/
structure SizeState where
  /--
  Contains terms of the form `USize.toBitVec e` and `ISize.toBitVec e` that we will translate to
  constant width `BitVec`.
  -/
  relevantTerms : Std.HashSet Expr := {}
  /--
  Contains all hypotheses that contain terms from `relevantTerms`
  -/
  relevantHyps : Std.HashSet FVarId := {}

private abbrev M := StateRefT SizeState MetaM

namespace M

@[inline]
private def addSizeTerm (e : Expr) : M Unit := do
  modify fun s => { s with relevantTerms := s.relevantTerms.insert e }

@[inline]
private def addSizeHyp (f : FVarId) : M Unit := do
  modify fun s => { s with relevantHyps := s.relevantHyps.insert f }

end M

public def intToBitVecPass : Pass where
  name := `intToBitVec
  run' goal := do
    let intToBvThms ← metaIntToBitVecExt.getTheorems
    let cfg ← PreProcessM.getConfig
    let simpCtx ← Simp.mkContext
      (config := {
        failIfUnchanged := false,
        zetaDelta := true,
        implicitDefEqProofs := false, -- leanprover/lean4/pull/7509
        maxSteps := cfg.maxSteps,
        instances := true
      })
      (simpTheorems := #[intToBvThms])
      (congrTheorems := (← getSimpCongrTheorems))

    let numBitsEq? ← findNumBitsEq goal
    let discharge? :=
      if let some (width, proof) := numBitsEq? then
        some <| fun prop => do
          let prop ← instantiateMVars prop
          let_expr Eq _ lhs rhs := prop | return none
          unless lhs.isConstOf ``System.Platform.numBits do return none
          let some val ← getNatValue? rhs | return none
          unless width == val do return none
          return some proof
      else
        none

    let hyps ← goal.getNondepPropHyps
    let ⟨result?, _⟩ ← simpGoal goal (ctx := simpCtx) (fvarIdsToSimp := hyps) (discharge? := discharge?)
    let some (_, goal) := result? | return none
    return goal
where
  /--
  Builds an expression of type: `System.Platform.numBits = const` from the hypotheses in the context
  if possible.
  -/
  findNumBitsEq (goal : MVarId) : MetaM (Option (Nat × Expr)) := do
    goal.withContext do
      for hyp in ← getPropHyps do
        match_expr ← instantiateMVars (← hyp.getType) with
        | Eq eqTyp lhs rhs =>
          if lhs.isConstOf ``System.Platform.numBits then
            let some val ← getNatValue? rhs | return none
            return some (val, mkFVar hyp)
          else if rhs.isConstOf ``System.Platform.numBits then
            let some val ← getNatValue? lhs | return none
            return some (val, mkApp4 (mkConst ``Eq.symm [1]) eqTyp lhs rhs (mkFVar hyp))
        | _ => continue
      return none

end Normalize
end Lean.Meta.Tactic.BVDecide
