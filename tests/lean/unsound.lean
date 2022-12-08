def foo (h : ∃ x: Nat, True) := h.1
theorem contradiction : False :=
  (by decide : 0 ≠ 1) (show foo ⟨0, trivial⟩ = foo ⟨1, trivial⟩ from rfl)
