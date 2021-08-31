def f (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | [a, b] => (a + b).succ
  | _ => 2

theorem ex (xs : List Nat) (hr : xs.reverse = xs) (ys : Nat) : ys > 0 → f xs > 0 := by
  simp [f]
  split
  next => intro hys; simp
  next => intro hys; simp; apply Nat.zero_lt_succ
  next zs n₁ n₂ =>
    intro hys
    rw [f.match_1.eq_3]
    anyGoals assumption
    decide
