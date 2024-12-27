example (a b : List Nat) : a = [] → b = [2] → a = b → False := by
  grind

example (a b : List Nat) : a = b → a = [] → b = [2] → False := by
  grind

example (a b : Bool) : a = true → b = false → a = b → False := by
  grind

example (a b : Sum Nat Bool) : a = .inl c → b = .inr true → a = b → False := by
  grind

example (a b : Sum Nat Bool) : a = b → a = .inl c → b = .inr true → a = b → False := by
  grind

inductive Foo (α : Type) : Nat → Type where
  | a (v : α) : Foo α 0
  | b (n : α) (m : Nat) (v : Vector Nat m) : Foo α (2*m)

example (h₁ : Foo.b x 2 v = f₁) (h₂ : Foo.b y 2 w = f₂) : f₁ = f₂ → x = y := by
  grind

example (h₁ : Foo.a x = f₁) (h₂ : Foo.a y = f₂) : f₁ = f₂ → x = y := by
  grind

example (h₁ : a :: b = x) (h₂ : c :: d = y) : x = y → a = c := by
  grind

example (h : x = y) (h₁ : a :: b = x) (h₂ : c :: d = y) : a = c := by
  grind

example (h : x = y) (h₁ : a :: b = x) (h₂ : c :: d = y) : b = d := by
  grind

example (a b : Sum Nat Bool) : a = .inl x → b = .inl y → x ≠ y → a = b → False := by
  grind
