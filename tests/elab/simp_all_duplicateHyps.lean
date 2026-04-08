axiom q : Nat → Prop
axiom p : Nat → Prop
axiom q_eq_p : q = p

example (h₁ : ¬ q 0) (h₂ : ¬ q 0) : ¬ p 0 := by
  trace_state
  /-
     h₁ : ¬ q 0
     h₂ : ¬ q 0
     ⊢ ¬ p 0
  -/
  simp_all
  /-
     h₂ : ¬ q 0
     ⊢ ¬ p 0
  -/
  trace_state
  rw [← q_eq_p]
  assumption
