example (a b c : nat) : a = b → b = c → c = a :=
begin
  tactic.intros,
  apply eq.symm,
  apply eq.trans,
  assumption,
  assumption
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  intro h1,
  intro h2,
  refine eq.symm (eq.trans h1 _),
  exact h2
end
