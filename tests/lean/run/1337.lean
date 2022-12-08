theorem n_minus_one_le_n {n : Nat} : n > 0 → n - 1 < n := by
  cases n with
  | zero => simp []
  | succ n =>
  intros
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  apply Nat.le.refl

partial def foo : Array Int → Int
  | arr => Id.run do
    let mut r : Int := 1
    while h : arr.size > 0 do
      r := r * arr[arr.size - 1]'(by apply n_minus_one_le_n h)
    return r
