def f {α} (a b : α) := a

theorem f_Eq {α} (a b : α) : f a b = a :=
  rfl

theorem ex1 (a b c : α) : f (f a b) c = a := by
  simp [f_Eq]

#print ex1

theorem ex2 (p : Nat → Bool) (x : Nat) (h : p x = true) : (if p x then 1 else 2) = 1 := by
  simp [h]

#print ex2
