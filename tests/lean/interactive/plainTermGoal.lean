
example : 0 < 2 :=
  Nat.ltTrans Nat.zeroLtOne (Nat.ltSuccSelf _)
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
  Nat.ltTrans _ _
              --^ $/lean/plainTermGoal

example : True := sorry
                --^ $/lean/plainTermGoal

example : ∀ n, n < n + 42 :=
  fun n => Nat.ltOfLeOfLt (Nat.leAddRight n 41) (Nat.ltSuccSelf _)
--^ $/lean/plainTermGoal
    --^ $/lean/plainTermGoal

example : ∀ n, n < 1 + n := by
  intro n
  rw [Nat.add_comm]
    --^ $/lean/plainTermGoal
  exact Nat.ltSuccSelf _
      --^ $/lean/plainTermGoal
