example : true :=
begin
  note H : true := (by trivial),
  exact H
end

example : true :=
begin
  note H : true := (by tactic.triv),
  exact H
end

meta example (h : tactic unit) : true :=
begin
  h, -- ERROR h should not be visible here
  trivial
end

example : false :=
begin
  note H : true := (by foo), -- ERROR
  exact sorry
end

constant P : Prop
example (p : P) : true :=
begin
  note H : P := by do { p ← tactic.get_local `p, tactic.exact p },
  trivial
end
