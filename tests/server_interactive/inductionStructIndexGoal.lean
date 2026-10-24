/-!
Tests that the goal shown before `induction` is the one before the tactic runs, not the one
after its targets have been generalized or its indices turned into variables.
-/

structure Wrap where
  inner : Nat

example {a b} (h : Relation.TransGen (fun a b : Wrap => a = b) (.mk a) (.mk b)) : a = b := by
  induction h with
--^ $/lean/plainGoal
  | single hr => grind
  | tail h hr ih => grind

example (n : Nat) : n + 0 = n := by
  induction n + 0 with
--^ $/lean/plainGoal
  | zero => rfl
  | succ _ _ => rfl

example (n : Nat) : n + 0 = n := by
  cases n + 0 with
--^ $/lean/plainGoal
  | zero => rfl
  | succ _ => rfl
