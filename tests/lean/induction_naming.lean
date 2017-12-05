example (a b : nat) : a + b = b + a :=
begin
  cases a,
  trace_state, /- `a` was used to name constructor field -/
  repeat { admit }
end

example (a b : nat) : a + b = b + a :=
begin
  induction a,
  trace_state, /- `a_n` and `a_ih` were used to name constructor fields -/
  repeat { admit }
end

set_option tactic.induction.concat_names false

example (a b : nat) : a + b = b + a :=
begin
  induction a,
  trace_state, /- `n` and `ih` were used to name constructor fields -/
  repeat { admit }
end
