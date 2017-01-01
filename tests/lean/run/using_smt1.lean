open smt_tactic tactic

example (a b c : nat) : a = c → a = b → b = c :=
by using_smt close

example (a b c : nat) : a = c → a = b → b = c :=
by using_smt (trace_state >> close)
