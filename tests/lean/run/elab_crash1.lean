open expr tactic

example (A : Type) (a : A) : A :=
by do to_expr `((sorry : A)) >>= exact

example (A : Type) (a : A) : A :=
by do refine `(sorry)

example (a : nat) : nat :=
by do to_expr `(nat.zero) >>= exact
