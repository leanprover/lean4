open tactic

example (p q : Prop) : p → q → q ∧ p :=
begin
  intros,
  constructor,
  trace_state,
  assumption,
  assumption
end
