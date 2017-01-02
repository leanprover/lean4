open smt_tactic tactic

example (a b c : nat) : a = c → a = b → b = c :=
by using_smt close

set_option pp.all true

example (a b c : nat) : a > nat.zero → a = c → a = b → b = c :=
by using_smt (trace_state >> close)

example (p q r : Prop) : p → q → ¬p → r :=
by using_smt (trace_state >> close)
