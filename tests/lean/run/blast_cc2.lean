set_option blast.init_depth 10
set_option blast.inc_depth 100
set_option blast.subst false

example (a b c d : nat) : a == b → b = c → c == d → a == d :=
by blast

example (a b c d : nat) : a = b → b = c → c == d → a == d :=
by blast

example (a b c d : nat) : a = b → b == c → c == d → a == d :=
by blast

example (a b c d : nat) : a == b → b == c → c = d → a == d :=
by blast

example (a b c d : nat) : a == b → b = c → c = d → a == d :=
by blast

example (a b c d : nat) : a = b → b = c → c = d → a == d :=
by blast

example (a b c d : nat) : a = b → b == c → c = d → a == d :=
by blast
