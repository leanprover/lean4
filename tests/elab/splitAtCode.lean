inductive Foo where
  | ctor1 (s : Nat)
  | ctor2 (s : String)

def test (x y : Foo) : Decidable (match (x, y) with
  | (.ctor1 s₁, .ctor1 s₂) => ¬s₁ = s₂
  | x => False) := by
 split <;> infer_instance
