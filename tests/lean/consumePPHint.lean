opaque p : Nat → Prop
opaque q : Nat → Prop

theorem p_of_q : q x → p x := sorry

theorem pletfun : p (let_fun x := 0; x + 1) := by
  -- ⊢ p (let_fun x := 0; x + 1)
  apply p_of_q
  trace_state -- `let_fun` hint should not be consumed.
  sorry
