/-!
This test used to check that metadata wasn't consumed by `apply`.
-/

opaque p : Nat → Prop
opaque q : Nat → Prop

theorem p_of_q : q x → p x := sorry

theorem pletfun : p (have x := 0; x + 1) := by
  -- ⊢ p (have x := 0; x + 1)
  apply p_of_q
  trace_state -- `have` should not be consumed.
  sorry
