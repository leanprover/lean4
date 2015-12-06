set_option blast.strategy "cc"

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
