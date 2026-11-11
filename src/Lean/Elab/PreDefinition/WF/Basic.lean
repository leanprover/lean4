/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Elab.Tactic.Basic

public section

namespace Lean.Elab.WF

register_builtin_option debug.rawDecreasingByGoal : Bool := {
  defValue := false
  descr    := "Shows the raw `decreasing_by` goal including internal implementation detail \
               instead of cleaning it up with the `clean_wf` tactic. Can be enabled for debugging \
               purposes. Please report an issue if you have to use this option for other reasons."
}

open Lean Meta Elab Tactic

/--
Beta-reduces, and reduces `PSum.casesOn` and `PSigma.casesOn` applied to constructors. This is how
the packed measure of a function block takes apart its packed argument.
-/
private partial def reducePacking (e : Expr) : Expr :=
  let e := e.headBeta
  if e.isAppOf ``PSum.casesOn && e.getAppNumArgs ≥ 6 then
    let args := e.getAppArgs
    let major := args[3]!
    if major.isAppOfArity ``PSum.inl 3 then
      reducePacking (mkAppN (.app args[4]! major.appArg!) args[6...*])
    else if major.isAppOfArity ``PSum.inr 3 then
      reducePacking (mkAppN (.app args[5]! major.appArg!) args[6...*])
    else
      e
  else if e.isAppOf ``PSigma.casesOn && e.getAppNumArgs ≥ 5 then
    let args := e.getAppArgs
    let major := args[3]!
    if major.isAppOfArity ``PSigma.mk 4 then
      reducePacking (mkAppN (mkApp2 args[4]! major.appFn!.appArg! major.appArg!) args[5...*])
    else
      e
  else
    e

/--
Rewrites a termination goal `(invImage f h).rel a b` to `h.rel (f a) (f b)`, and `InvImage r f a b`
(used for `Nat`-valued measures) to `r (f a) (f b)`, reducing the unpacking of `a` and `b` in
`f a` and `f b`. The measure `f` of a function block is a case split over all its functions, so
this keeps the goal that `clean_wf` sees independent of the size of the block.
-/
def applyMeasure (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType
  let targetNew? := match target with
    | .app (.app (.proj ``WellFoundedRelation 0 wfRel) a) b =>
      match_expr wfRel with
      | invImage _ β f h =>
        let u := wfRel.getAppFn.constLevels![1]!
        some (mkApp4 (mkConst ``WellFoundedRelation.rel [u]) β h
          (reducePacking (.app f a)) (reducePacking (.app f b)))
      | _ => none
    | _ =>
      match_expr target with
      | InvImage _ _ r f a b =>
        some (mkApp2 r (reducePacking (.app f a)) (reducePacking (.app f b))).headBeta
      | _ => none
  let some targetNew := targetNew? | return mvarId
  -- Without a type hint, the auxiliary lemmas that the termination proofs are abstracted into get
  -- the new, small type rather than one that mentions the measure of the whole block.
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew (← mvarId.getTag)
  mvarId.assign mvarNew
  return mvarNew.mvarId!

def applyCleanWfTactic : TacticM Unit := do
  unless debug.rawDecreasingByGoal.get (← getOptions) do
    setGoals (← (← getGoals).mapM (applyMeasure ·))
    Tactic.evalTactic (← `(tactic| all_goals clean_wf))

end Lean.Elab.WF
