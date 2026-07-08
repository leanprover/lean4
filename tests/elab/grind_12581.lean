-- Testing conjunction of grind-provable goals
-- See https://github.com/leanprover/lean4/issues/12581

-- `grind` should be able to prove a conjunction of things it can prove individually
example {a b c d : Int} (f : Int → Nat → Int) (h₁ : a = 0) (h₁' : ∀ k, 0 ≤ f c k) (h₂ : b = 0) (h₂' : ∀ k, 0 ≤ f d k) :
    a + b = 0 ∧ ∀ k, 0 ≤ f c k + f d k := by
  grind
