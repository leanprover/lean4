-- Projection to the witness should be rejected.
def witness : Nat := (⟨1, Nat.le_refl _⟩ : ∃ x, x ≥ 1).1

-- Projection to the property as well (it could contain the witness projection).
theorem witness_eq (h : ∃ x : Nat, True) : h.2 = h.2 := rfl
