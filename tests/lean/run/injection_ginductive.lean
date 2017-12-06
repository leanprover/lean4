inductive term
| const (n : string) : term
| app (fn : string) (args : list term) : term

constant p : Prop → Prop
axiom p_ax : ∀ x, p x = x

example (f₁ f₂ : string) (as₁ as₂ : list term) (h : term.app f₁ as₁ = term.app f₂ as₂) : p (as₁ = as₂) :=
begin
  injection h,
  trace_state,
  guard_hyp h_1 := f₁ = f₂,
  guard_hyp h_2 := as₁ = as₂,
  rw p_ax,
  assumption
end
