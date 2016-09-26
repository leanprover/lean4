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
  tactic.intro `h1,
  tactic.intros,
  refine eq.symm (eq.trans h1 _),
  assumption
end
