#exit

example (x y : Nat) (h : x = y) : 0 + x = y + 0 := by
  have := by exact h.symm
  /-
    Bad: we get "Goals accomplished" here
    Should be:
    ... |- 0 + x = y + 0
  -/

example (x : Nat) : x = 0 + (0 + (0 + x)) ∧ p := by
  constructor
  · cases x
    next => rfl                --v Good: we get multiple states here as expected
    next => repeat rw [Nat.zero_add] /- Good: we get the correct behavior here: Goals accomplished. -/
  /-
    Bad: We get "Goals accomplished" here
    Should be:
    ... |- p
  -/

example (x : Nat) : x = 0 + (0 + (0 + x)) ∧ p := by
  constructor
  match x with
  | 0 => rfl
  | y+1 => repeat rw [Nat.zero_add] /- Good: We get the correct behavior here: Goals accomplished. -/
       --^ Bad: get the `match` tactic initial state here.
  -- Bad: we get "Goals accomplished" here
