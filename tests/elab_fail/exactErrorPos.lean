set_option pp.rawOnError true

theorem ex1 (f : Nat → Nat) (x : Nat) (h1 : (x : Nat) → x > 0 → f x = x) (h2 : x > 0) : f x = x := by
  exact h1 _ _

theorem ex2 (f : Nat → Nat) (x : Nat) (h1 : (x : Nat) → x > 0 → f x = x) (h2 : x > 0) : f x = x := by
  refine h1 _ _

theorem ex3 (f : Nat → Nat) (x : Nat) (h1 : (x : Nat) → x > 0 → f x = x) (h2 : x > 0) : f x = x := by
  first | exact h1 _ _ | apply h1
  assumption

theorem ex4 (f : Nat → Nat) (x : Nat) (h1 : (x : Nat) → x > 0 → f x = x) (h2 : x > 0) : f x = x := by
  first | refine h1 _ _ | apply h1
  assumption

theorem ex5 (f g : Nat → Nat) (x : Nat) (h1 : (x : Nat) → x > 0 → f x = x) (h2 : x > 0) (h3 : g x = x) : f x = x := by
  first | apply h3 | apply h1
  assumption

theorem ex6 (f : Nat → Nat) (x : Nat) (h1 : (x : Nat) → x > 0 → f x = x) (h2 : x > 0) : f x = x := by
  first | refine h1 _ _ | refine h1 _ _
  assumption
