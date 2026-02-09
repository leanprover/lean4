def f (x y : Nat) :=
  match x with
  | 0   => y + 1
  | n+1 => y + 1

private theorem matchEq (x y : Nat) :
  (match x with
   | 0   => y + 1
   | n+1 => y + 1) = y + 1 := by
  cases x <;> simp

theorem fex1 : f x y = y + 1 := by
  simp [f, matchEq]

theorem fex2 : f x y = y + 1 := by
  simp [f]
  rw [matchEq]
