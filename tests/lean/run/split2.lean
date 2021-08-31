def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → f x y z = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

example (x y z : Nat) : f x y z = y ∨ f x y z = 1 := by
  intros
  simp [f]
  split
  . exact Or.inl rfl
  . exact Or.inl rfl
  . exact Or.inl rfl
  . exact Or.inr rfl

example (x y z : Nat) : f x y z = y ∨ f x y z = 1 := by
  intros
  simp [f]
  split <;> (first | apply Or.inl rfl | apply Or.inr rfl)

def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => Nat.succ (a+b)
  | _, [b, c] => Nat.succ b
  | _, _   => 1

example (xs ys : List Nat) : g xs ys > 0 := by
  simp [g]
  split
  next a b _    => show Nat.succ (a + b) > 0; apply Nat.zero_lt_succ
  next xs b c _ => show Nat.succ b > 0; apply Nat.zero_lt_succ
  next => decide
