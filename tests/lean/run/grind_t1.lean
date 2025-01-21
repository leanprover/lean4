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

example (a b : Nat) : a = 1 → b = 2 → a = b → False := by
  grind

example (a b c : Int) : a = 1 → c = -2 → a = b → c = b → False := by
  grind

example (a b : Char) : a = 'h' → b = 'w' → a = b → False := by
  grind

example (a b : String) : a = "hello" → b = "world" → a = b → False := by
  grind

example (a b c : String) : a = c → a = "hello" → c = "world" → c = b → False := by
  grind

example (a b c : BitVec 32) : a = c → a = 1#32 → c = 2#32 → c = b → False := by
  grind

example (a b c : UInt32) : a = c → a = 1 → c = 200 → c = b → False := by
  grind

structure Boo (α : Type) where
  a : α
  b : α
  c : α

example (a b d : Nat) (f : Nat → Boo Nat) : (f d).1 ≠ a → f d = ⟨b, v₁, v₂⟩ → b = a → False := by
  grind

def ex (a b c d : Nat) (f : Nat → Boo Nat) : (f d).2 ≠ a → f d = ⟨b, c, v₂⟩ → c = a → False := by
  grind

example (a b c : Nat) (f : Nat → Nat) : { a := f b, c, b := 4 : Boo Nat }.1 ≠ f a → f b = f c → a = c → False := by
  grind

example (a b c : Nat) (f : Nat → Nat) : p = { a := f b, c, b := 4 : Boo Nat } → p.1 ≠ f a → f b = f c → a = c → False := by
  grind

example (a b c : Nat) (f : Nat → Nat) : p.1 ≠ f a → p = { a := f b, c, b := 4 : Boo Nat } → f b = f c → a = c → False := by
  grind
