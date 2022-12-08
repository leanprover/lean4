def f (xs : List Nat) : Nat :=
  match xs with
  | [] => 1
  | [a, b] => (a + b).succ
  | _ => 2

theorem ex1 (xs : List Nat) (hr : xs.reverse = xs) (ys : Nat) : ys > 0 → f xs > 0 := by
  simp [f]
  split
  next => intro hys; decide
  next => intro hys; apply Nat.zero_lt_succ
  next zs n₁ n₂ => intro hys; decide

def g (xs : List Nat) : Nat :=
  match xs with
  | [a, b, c, d, e] => a + e + 1
  | _               => 1

theorem ex2 (xs : List Nat) : g xs > 0 := by
  simp [g]
  split
  next a b c d e => apply Nat.zero_lt_succ
  next h => decide
