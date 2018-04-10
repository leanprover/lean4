example (p q : Prop) (h₀ : q) : ∀ (h : p ∧ true), q :=
begin
  simp, intros,
  trace_state,
  guard_hyp h := p,
  exact h₀
end
