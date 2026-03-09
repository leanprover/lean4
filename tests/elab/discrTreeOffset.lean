def f (x : Nat) (y : Nat) :=
  3 + x

def g (x : Nat) := x*x*x

@[simp] theorem eq1 (x y : Nat) : f (x+2) y = x+5 := by
  simp [f]
  rw [Nat.add_left_comm]

theorem ex1 : g (f (x+3) y) = g (x+6) := by
  simp

theorem ex2 : g (f (x.succ.succ) y) = g (x+5) := by
  simp

theorem ex3 : g (f 3 y) = g 6 := by
  simp

theorem ex4 : g (f 2 y) = g 5 := by
  simp

theorem ex5 : g (f (x.succ.succ.succ) y) = g (x+6) := by
  simp

def h (x : Nat) : Type :=
  match x with
  | 0 => Nat
  | _ => Unit

@[simp] theorem h_zero : h 0 = Nat :=
  rfl

theorem ex6 : h Nat.zero = Nat := by
  simp
