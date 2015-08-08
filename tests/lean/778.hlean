open bool
definition is_equiv_bnot : is_equiv bnot :=
begin
  fapply is_equiv.mk,
    exact bnot,
    all_goals (intro b;cases b),
    state,
    repeat reflexivity
end
