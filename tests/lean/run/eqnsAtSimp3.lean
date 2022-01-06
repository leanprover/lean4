def f (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * f x 0
  | x+1, y => 2 * f x y

theorem ex1 (x : Nat) (y : Nat) (h : y ≠ 5) : ∃ z, f (x+1) y = 2 * z := by
  simp [f, h]
  trace_state
  apply Exists.intro
  rfl

@[simp] def g (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * g x 0
  | x+1, y => 2 * g x y

theorem ex2 (x : Nat) (y : Nat) (h : y ≠ 5) : ∃ z, g (x+1) y = 2 * z := by
  simp [h]
  trace_state
  apply Exists.intro
  rfl
