--
example : 0 < 2 :=
  Nat.lt_trans Nat.zero_lt_one (Nat.lt_succ_self _)
            --^ termGoal
             --^ termGoal
              --^ termGoal
                             --^ termGoal
                                              --^ termGoal

example : Option Unit := do
  let y : Int ← none
  let x := Nat.zero
        --^ termGoal
  return ()

example (m n : Nat) : m < n :=
  Nat.lt_trans _ _
               --^ termGoal
                --^ termGoal

example : True := sorry
                --^ termGoal

example : ∀ n, n < n + 42 :=
  fun n => Nat.lt_of_le_of_lt (Nat.le_add_right n 41) (Nat.lt_succ_self _)
--^ termGoal
    --^ termGoal

example : ∀ n, n < 1 + n := by
  intro n
  rw [Nat.add_comm]
    --^ termGoal
  exact Nat.lt_succ_self _
      --^ termGoal

#check fun (n m : Nat) => m
            --^ termGoal
