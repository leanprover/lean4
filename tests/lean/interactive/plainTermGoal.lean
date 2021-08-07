--
example : 0 < 2 :=
  Nat.lt_trans Nat.zero_lt_one (Nat.lt_succ_self _)
            --^ $/lean/plainTermGoal
             --^ $/lean/plainTermGoal
              --^ $/lean/plainTermGoal
                             --^ $/lean/plainTermGoal
                                              --^ $/lean/plainTermGoal

example : OptionM Unit := do
  let y : Int ← none
  let x ← Nat.zero
        --^ $/lean/plainTermGoal
  return ()

example (m n : Nat) : m < n :=
  Nat.lt_trans _ _
               --^ $/lean/plainTermGoal

example : True := sorry
                --^ $/lean/plainTermGoal

example : ∀ n, n < n + 42 :=
  fun n => Nat.lt_of_le_of_lt (Nat.le_add_right n 41) (Nat.lt_succ_self _)
--^ $/lean/plainTermGoal
    --^ $/lean/plainTermGoal

example : ∀ n, n < 1 + n := by
  intro n
  rw [Nat.add_comm]
    --^ $/lean/plainTermGoal
  exact Nat.lt_succ_self _
      --^ $/lean/plainTermGoal

#check fun (n m : Nat) => m
            --^ $/lean/plainTermGoal
