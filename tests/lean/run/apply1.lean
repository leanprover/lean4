open tactic

example (p q : Prop) : p → q → p ∧ q :=
by do
  intros,
  apply (expr.const `and.intro []),
  trace_state,
  all_goals assumption
