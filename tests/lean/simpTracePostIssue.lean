def f (x : Nat) := 0 + x

@[simp ↓]
theorem f_eq : f x = x := by simp [f]

set_option tactic.simp.trace true in
example : f (f x) = x := by
  simp

example : f (f x) = x := by
  simp only [↓f_eq]
