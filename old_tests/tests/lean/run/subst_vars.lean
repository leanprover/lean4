open tactic

example (a b c d : nat) : a = b → b = c → d = c → a = d :=
by intros; subst_vars
