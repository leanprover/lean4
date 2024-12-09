def zero_out (arr : Array Nat) (i : Nat) : Array Nat :=
  if h : i < arr.size then
    zero_out (arr.set i 0) (i + 1)
  else
    arr
termination_by arr.size - i
decreasing_by simp; apply Nat.sub_succ_lt_self _ _ h

-- set_option trace.Elab.definition true
theorem size_zero_out (arr : Array Nat) (i : Nat) : (zero_out arr i).size = arr.size := by
  unfold zero_out
  split
  · rw [size_zero_out]
    rw [Array.size_set]
  · rfl
termination_by arr.size - i
decreasing_by simp; apply Nat.sub_succ_lt_self; assumption
