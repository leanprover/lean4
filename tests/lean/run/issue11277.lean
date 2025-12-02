

inductive F : Nat → Type where
  | zero : F n
  | succ : F n → F (n + 1)

def foo : F n → Nat
  | .zero => 0
  -- | x@(.succ i) => 1 + foo i
  | .succ i => 1 + foo i

def bar : F n → Nat
  | .zero => 0
  | .succ i => 1 + bar i

theorem baz (xs : F n) : foo xs = bar xs := by
  unfold foo
  split
  next =>
    simp [bar]
  next z zs =>
    rw [bar]
    have := baz zs
    grind
termination_by foo xs
decreasing_by
  skip
  subst ‹n = _›
  have := eq_of_heq ‹_›
  subst this
  grind [foo]
