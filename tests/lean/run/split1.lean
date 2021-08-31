def f (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | [a, b] => (a + b).succ
  | _ => 2

theorem ex1 (xs : List Nat) (hr : xs.reverse = xs) (ys : Nat) : ys > 0 → f xs > 0 := by
  simp [f]
  split
  next => intro hys; simp
  next => intro hys; simp; apply Nat.zero_lt_succ
  next zs n₁ n₂ =>
    intro hys
    rw [f.match_1.eq_3]
    anyGoals assumption
    decide

def g (xs : List Nat) : Nat :=
  match xs with
  | [a, b, c, d, e] => a + e + 1
  | _               => 1

theorem ex2 (xs : List Nat) : g xs > 0 := by
  simp [g]
  split
  . simp; apply Nat.zero_lt_succ
  . rw [g.match_1.eq_2]
    . decide
    . assumption
