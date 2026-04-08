set_option trace.Elab.info true
example (x y : Nat) (h : x = y) : 0 + x = y + 0 := by
  have := by exact h.symm
--
--^ $/lean/plainGoal
-- Good: ..., this : y = x |- 0 + x = y + 0

example (x : Nat) : x = 0 + (0 + (0 + x)) ∧ p := by
  constructor
  · cases x
    next => rfl
                               -- Good: we get multiple states here as expected
                               --v $/lean/plainGoal
    next => repeat rw [Nat.zero_add]
                                  --^ $/lean/plainGoal
                                  -- Bad? We still get all states except the one closed by implicit `rfl`
--^ $/lean/plainGoal
-- Good: ... |- p

example (x : Nat) : x = 0 + (0 + (0 + x)) ∧ p := by
  constructor
  match x with
  | 0 => rfl
                                 -- Bad? We still get all states except the one closed by implicit `rfl`
                                 --v $/lean/plainGoal
  | y+1 => repeat rw [Nat.zero_add]
       --^ $/lean/plainGoal
       -- Good: we get the succ state here
--^ $/lean/plainGoal
-- Good:  ... |- p
