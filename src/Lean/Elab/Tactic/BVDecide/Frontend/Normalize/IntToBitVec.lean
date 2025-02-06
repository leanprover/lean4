/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
import Lean.Elab.Tactic.BVDecide.Frontend.Attr
import Lean.Elab.Tactic.Simp

/-!
This module contains the implementation of the pre processing pass for reducing `UIntX`/`IntX` to
`BitVec` and thus allow `bv_decide` to reason about them.

It:
1. runs the `int_toBitVec` simp set
2. If `USize.toBitVec` is used anywhere looks for equations of the form
   `System.Platform.numBits = constant` (or flipped) and uses them to convert the system back to
   fixed width.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

/--
Contains information for the `USize` elimination pass.
-/
structure USizeState where
  /--
  Contains terms of the form `USize.toBitVec e` that we will translate to constant width `BitVec`.
  -/
  relevantTerms : Std.HashSet Expr := {}
  /--
  Contains all hypotheses that contain terms from `relevantTerms`
  -/
  relevantHyps : Std.HashSet FVarId := {}

private abbrev M := StateRefT USizeState MetaM

namespace M

@[inline]
def addUSizeTerm (e : Expr) : M Unit := do
  modify fun s => { s with relevantTerms := s.relevantTerms.insert e }

@[inline]
def addUSizeHyp (f : FVarId) : M Unit := do
  modify fun s => { s with relevantHyps := s.relevantHyps.insert f }

end M

def intToBitVecPass : Pass where
  name := `intToBitVec
  run' goal := do
    let intToBvThms ← intToBitVecExt.getTheorems
    let cfg ← PreProcessM.getConfig
    let simpCtx ← Simp.mkContext
      (config := { failIfUnchanged := false, zetaDelta := true, maxSteps := cfg.maxSteps })
      (simpTheorems := #[intToBvThms])
      (congrTheorems := (← getSimpCongrTheorems))

    let hyps ← goal.getNondepPropHyps
    let ⟨result?, _⟩ ← simpGoal goal (ctx := simpCtx) (fvarIdsToSimp := hyps)
    let some (_, goal) := result? | return none
    handleUSize goal |>.run' {}
where
  handleUSize (goal : MVarId) : M MVarId := do
    if ← detectUSize goal then
      replaceUSize goal
    else
      return goal

  detectUSize (goal : MVarId) : M Bool := do
    goal.withContext do
      for hyp in ← getPropHyps do
        (← hyp.getType).forEachWhere
          (stopWhenVisited := true)
          (·.isAppOfArity ``USize.toBitVec 1)
          fun e => do
            M.addUSizeTerm e
            M.addUSizeHyp hyp

      return !(← get).relevantTerms.isEmpty

  /--
  Turn `goal` into a goal containing `BitVec const` instead of `USize`.
  -/
  replaceUSize (goal : MVarId) : M MVarId := do
    if let some (numBits, numBitsEq) ← findNumBitsEq goal then
      goal.withContext do
        let relevantHyps := (← get).relevantHyps.toArray.map mkFVar
        let relevantTerms := (← get).relevantTerms.toArray
        let (app, abstractedHyps) ← liftMkBindingM <| MetavarContext.revert relevantHyps goal true
        let newMVar := app.getAppFn.mvarId!
        let targetType ← newMVar.getType
        /-
        newMVar has type : h1 → h2 → ... → False`
        This code computes a motive of the form:
        ```
        fun z _ => ∀ (x_1 : BitVec z) (x_2 : BitVec z) ..., h1 → h2 → ... → False
        ```
        Where:
        - all terms from `relevantTerms` in the implication are substituted by `x_1`, ...
        - all occurences of `numBits` are substituted by `z`

        Additionally we compute a new metavariable with type:
        ```
        ∀ (x_1 : BitVec const) (x_2 : BitVec const) ..., h1 → h2 → ... → False
        ```
        with all occurences of `numBits` substituted by const. This meta variable is going to become
        the next goal
        -/
        let (motive, newGoalType) ←
          withLocalDeclD `z (mkConst ``Nat) fun z => do
            let otherArgType := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (toExpr numBits) z
            withLocalDeclD `h otherArgType fun other => do
              let argType := mkApp (mkConst ``BitVec) z
              let argTypes := relevantTerms.map (fun _ => (`x, argType))
              let innerMotiveType ←
                withLocalDeclsDND argTypes fun args => do
                  let mut subst : Std.HashMap Expr Expr := Std.HashMap.empty (args.size + 1)
                  subst := subst.insert (mkConst ``System.Platform.numBits) z
                  for term in relevantTerms, arg in args do
                    subst := subst.insert term arg
                  let motiveType := targetType.replace subst.get?
                  mkForallFVars args motiveType
              let newGoalType := innerMotiveType.replaceFVar z (toExpr numBits)
              let motive ← mkLambdaFVars #[z, other] innerMotiveType
              return (motive, newGoalType)
        let mut newGoal := (← mkFreshExprMVar newGoalType).mvarId!
        let casesOn := mkApp6 (mkConst ``Eq.casesOn [0, 1])
          (mkConst ``Nat)
          (toExpr numBits)
          motive
          (mkConst ``System.Platform.numBits)
          numBitsEq
          (mkMVar newGoal)
        goal.assign <| mkAppN casesOn (relevantTerms ++ abstractedHyps)
        -- remove all of the hold hypotheses about USize.toBitVec to prevent false counter examples
        (newGoal, _) ← newGoal.tryClearMany' (abstractedHyps.map Expr.fvarId!)
        -- intro both the new `BitVec const` as well as all hypotheses about them
        (_, newGoal) ← newGoal.introN (relevantTerms.size + abstractedHyps.size)
        return newGoal
    else
      logWarning m!"Detected USize in the goal but no hypothesis about System.Platform.numBits, consider case splitting on {mkConst ``System.Platform.numBits_eq}"
      return goal

  /--
  Builds an expression of type: `const = System.Platform.numBits` from the hypotheses in the context
  if possible.
  -/
  findNumBitsEq (goal : MVarId) : MetaM (Option (Nat × Expr)) := do
    goal.withContext do
      for hyp in ← getPropHyps do
        match_expr ← hyp.getType with
        | Eq eqTyp lhs rhs =>
          if lhs.isConstOf ``System.Platform.numBits then
            let some val ← getNatValue? rhs | return none
            return some (val, mkApp4 (mkConst ``Eq.symm [1]) eqTyp lhs rhs (mkFVar hyp))
          else if rhs.isConstOf ``System.Platform.numBits then
            let some val ← getNatValue? lhs | return none
            return some (val, mkFVar hyp)
        | _ => continue
      return none

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
