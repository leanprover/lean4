example (p q r s: Prop): p ∧ q → r ∧ s → s ∧ q :=
begin
  intros h1 h2,
  cases h1,
  cases h2,
  trace_state,
  constructor; assumption
end

example (p q r s: Prop): p ∧ q → r ∧ s → s ∧ q :=
begin
  intros a a_1,
  cases a,
  cases a_1,
  trace_state,
  constructor; assumption
end

#print "------------"

example (p q r s: Prop): p ∧ q → r ∧ s → s ∧ q :=
begin
  intros h1 h2,
  induction h1,
  induction h2,
  trace_state,
  constructor; assumption
end

example (p q r s: Prop): p ∧ q → r ∧ s → s ∧ q :=
begin
  intros a a_1,
  induction a,
  induction a_1,
  trace_state,
  constructor; assumption
end
