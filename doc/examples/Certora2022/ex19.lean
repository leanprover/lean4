/- Tactic combinators -/

example : p → q → r → p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  intros
  repeat (any_goals constructor)
  all_goals assumption

example : p → q → r → p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  intros
  repeat (any_goals (first | assumption | constructor))
