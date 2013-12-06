Theorem T2 (a b : Bool) : a => b => a /\ b.
apply imp_tactic.
apply imp_tactic2.
foo.
apply imp_tactic.
abort.

Variables a b : Bool.
Show Environment 2.
