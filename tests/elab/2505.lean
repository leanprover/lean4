import Lean

open Lean Elab Tactic Meta

inductive A : Nat → Prop

def Lean.MVarId.getType'' (mvarId : MVarId) : MetaM Expr := do
  instantiateMVars (← whnf (← mvarId.getType))

elab "the_target" : tactic => Tactic.withMainContext do
  dbg_trace "target : {← (← getMainGoal).getType'}"
  dbg_trace "target' : {← (← getMainGoal).getType''}"

example : True := by
  let p := A ?n
  case n => exact 1
  have : p := ?h
  case h =>
    the_target
    sorry
  sorry
/-
Prior to #2595, this gave:

target : A ?_uniq.3033
target' : A (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
-/
