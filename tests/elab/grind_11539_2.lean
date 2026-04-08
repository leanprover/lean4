example (a b : Nat) (f g : Nat → Nat)
    (hf : (∀ i ≤ a, f i ≤ f (i + 1)) ∧ f 0 = 0)
    (hg : (∀ i ≤ b, g i ≤ g (i + 1)) ∧ g 0 = 0 ∧ g b = 0) :
    g (a + b - a) = 0 := by
  grind
