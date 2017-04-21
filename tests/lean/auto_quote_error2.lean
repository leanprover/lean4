example (a b c : nat) : a = b → b = c → c = a :=
begin
  tactic.intros,
  apply eq.symm,
  apply eq.refl, -- Error: unification
  assumption,
  assumption
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  tactic.intros,
  apply eq.symm,
  begin
    tactic.trace "hello world",
  end, -- Error unsolved goals
  assumption,
  assumption
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  tactic.intros,
  apply eq.symm,
  apply eq.trans,
  begin
    tactic.trace "hello world",
  end, -- Error unsolved goals (remark: nested 'begin ... end' blocks focus on the main goal)
  assumption
end

example (a b c : nat) : a = b → b = c → c = a :=
begin
  intro h1, intro h2,
  apply eq.symm,
  begin
    exact eq.trans h1 _, -- Error unsolved
  end,
end

example (a b : nat) : a = 0 → b = 0 → a = b ∧ b = a :=
begin
   intros h1 h2,
   split,
   { subst h1 },
            --^ error should be at `}`
end
