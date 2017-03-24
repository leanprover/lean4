def p (a : nat) (b := tt) : nat :=
a + cond b 1 2

def q (a b : nat) (h : a ≠ b . tactic.contradiction) : nat :=
a + b

def val1 : nat :=
begin
  apply @p,
  exact 2,
  apply_opt_param
end

example : val1 = 3 :=
rfl

def val2 : nat :=
begin
  fapply @q,
  exact 1,
  exact 0,
  apply_auto_param
end

example : val2 = 1 :=
rfl
