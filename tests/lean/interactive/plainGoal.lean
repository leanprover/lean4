example : α → α := by
                  --^ $/lean/plainGoal
                   --^ $/lean/plainGoal
  intro a
--^ $/lean/plainGoal
 --^ $/lean/plainGoal
 --v $/lean/plainGoal
  focus
    apply a

example : α → α := by
                  --^ $/lean/plainGoal

example : 0 + n = n := by
  induction n with
  | zero => simp; simp
       --^ $/lean/plainGoal
  | succ
   --^ $/lean/plainGoal

example : α → α := by
  intro a; apply a
       --^ $/lean/plainGoal
