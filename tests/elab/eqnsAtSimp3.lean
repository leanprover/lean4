def f (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * f x 0
  | x+1, y => 2 * f x y

/--
trace: x y : Nat
h : y ≠ 5
⊢ ∃ z, 2 * f x y = 2 * z
-/
#guard_msgs in
theorem ex1 (x : Nat) (y : Nat) (h : y ≠ 5) : ∃ z, f (x+1) y = 2 * z := by
  simp [f]
  trace_state
  apply Exists.intro
  rfl

@[simp] def g (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * g x 0
  | x+1, y => 2 * g x y

/--
trace: x y : Nat
h : y ≠ 5
⊢ ∃ z, 2 * g x y = 2 * z
-/
#guard_msgs in
theorem ex2 (x : Nat) (y : Nat) (h : y ≠ 5) : ∃ z, g (x+1) y = 2 * z := by
  simp
  trace_state
  apply Exists.intro
  rfl

/--
trace: x y : Nat
h : y = 5 → False
⊢ ∃ z, 2 * f x y = 2 * z
-/
#guard_msgs in
theorem ex3 (x : Nat) (y : Nat) (h : y = 5 → False) : ∃ z, f (x+1) y = 2 * z := by
  simp [f]
  trace_state
  apply Exists.intro
  rfl

@[simp] def f2 (x y z : Nat) : Nat :=
  match x, y, z with
  | 0,   0, 0 => 1
  | 0,   y, _ => y
  | x+1, 5, 6 => 2 * f2 x 0 1
  | x+1, y, z => 2 * f2 x y z


#check f2.eq_4

/--
trace: x y z : Nat
h : y = 5 → z = 6 → False
⊢ ∃ w, 2 * f2 x y z = 2 * w
-/
#guard_msgs in
theorem ex4 (x y z : Nat) (h : y = 5 → z = 6 → False) : ∃ w, f2 (x+1) y z = 2 * w := by
  simp [f2]
  trace_state
  apply Exists.intro
  rfl

theorem ex5 (x y z : Nat) (h1 : y ≠ 5) : ∃ w, f2 (x+1) y z = 2 * w := by
  simp [f2, h1]
  apply Exists.intro
  rfl

theorem ex6 (x y z : Nat) (h2 : z ≠ 6) : ∃ w, f2 (x+1) y z = 2 * w := by
  simp [f2, h2]
  apply Exists.intro
  rfl

@[simp] def f3 (x y z : Nat) : Nat :=
  match x, y, z with
  | 0,   0, 0 => 1
  | 0,   y, _ => y
  | x+1, 5, 6 => 4 * f3 x 0 1
  | x+1, 6, 4 => 3 * f3 x 0 1
  | x+1, y, z => 2 * f3 x y z

#check f3.eq_5

theorem ex7 (x y z : Nat) (h2 : z ≠ 6) (h3 : y ≠ 6) : ∃ w, f3 (x+1) y z = 2 * w := by
  simp [f3, h2,  h3]
  apply Exists.intro
  rfl

theorem ex8 (x y z : Nat) (h2 : y = 5 → z = 6 → False) (h3 : y = 6 → z = 4 → False) : ∃ w, f3 (x+1) y z = 2 * w := by
  simp [f3]
  apply Exists.intro
  rfl
