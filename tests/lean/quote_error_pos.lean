open tactic

meta def apply_zero_add (a : pexpr) : tactic unit :=
to_expr `(zero_add %%a) >>= exact

example (a : nat) : 0 + a = a :=
begin
  apply_zero_add `(tt), -- Error should be here
end

meta def apply_zero_add2 (a : pexpr) : tactic unit :=
`[apply zero_add %%a]

example (a : nat) : 0 + a = a :=
begin
  apply_zero_add2 `(tt), -- Error should be here
end
