open expr tactic

meta definition to_expr_target (a : pexpr) : tactic expr :=
do tgt ← target,
   to_expr `((%%a : %%tgt))

noncomputable example (A : Type) (a : A) : A :=
by do to_expr_target `(sorry) >>= exact

noncomputable example (A : Type) (a : A) : A :=
by do refine `(sorry)

example (a : nat) : nat :=
by do to_expr `(nat.zero) >>= exact
