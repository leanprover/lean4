example (a : Array α) (x : α) (i : Nat) (h : i < a.size) :
    haveI : i < (a.push x).size := by simp [*, Nat.lt_succ_of_le, Nat.le_of_lt]
    (a.push x)[i] = a[i] := by
  sorry
