Theorem T2 (a b : Bool) : a => b => a /\ b.
apply imp_tac.
apply imp_tac2.
foo.
apply imp_tac.
abort.

Variables a b : Bool.
Show Environment 2.
