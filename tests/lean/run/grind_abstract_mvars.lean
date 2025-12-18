module
example (xs : Array Nat)
    (w : ∀ (j : Nat), 0 ≤ j → ∀ (x : j < xs.size / 2), xs[j] = xs[xs.size - 1 - j])
    (i : Nat) (hi₁ : i < xs.reverse.size) (hi₂ : i < xs.size) (h : i < xs.size / 2) : xs.reverse[i] = xs[i] := by
  rw [w] <;> grind
