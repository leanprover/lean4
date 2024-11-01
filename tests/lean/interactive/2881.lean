example (n : Nat) : True := by
  induction n
  case zero => sorry -- `zero` goal
 --^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n
  case zero => sorry
     -- `succ` goal
--^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n
  case' zero => sorry -- `zero` goal
 --^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n
  case' zero => sorry
     -- `succ` goal
--^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n
  next => sorry -- `zero` goal
 --^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n
  next => sorry
     -- `succ` goal
--^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n with
  | zero => sorry -- `zero` goal
 --^ $/lean/plainGoal

example (n : Nat) : True := by
  induction n with
  | zero => sorry
    -- General goal
--^ $/lean/plainGoal

example : True := by
  suffices True by
      -- Goal assuming `True`
  --^ $/lean/plainGoal
    sorry
