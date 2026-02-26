syntax "foo" : tactic

macro_rules | `(tactic| foo) => `(tactic| assumption)
macro_rules | `(tactic| foo) => `(tactic| apply Nat.pred_lt; assumption)
macro_rules | `(tactic| foo) => `(tactic| contradiction)

example (i : Nat) (h : i - 1 < i) : i - 1 < i := by
  foo

example (i : Nat) (h : i ≠ 0) : i - 1 < i := by
  foo

example (i : Nat) (h : False) : i - 1 < i := by
  foo
