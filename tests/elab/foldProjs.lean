import Lean.Meta.Tactic.Grind
import Lean.Elab.Tactic

structure A (α : Type u) where
  x : α
  y : α
  f : α → α

structure B (α : Type u) extends A α where
  z : α
  b : Bool

open Lean Meta Elab Tactic
elab "fold_projs" : tactic => liftMetaTactic1 fun mvarId => do
  mvarId.replaceTargetDefEq (← Grind.foldProjs (← mvarId.getType))

example (a : Nat × Bool) : a.fst = 10 := by
  unfold Prod.fst
  fail_if_success guard_target =ₛ  a.fst = 10
  fold_projs
  guard_target =ₛ  a.fst = 10
  sorry

example (b : B (List Nat)) : b.y = [] := by
  unfold B.toA
  unfold A.y
  fail_if_success unfold A.y
  fail_if_success guard_target =ₛ  b.y = []
  fold_projs
  guard_target =ₛ  b.y = []
  sorry
