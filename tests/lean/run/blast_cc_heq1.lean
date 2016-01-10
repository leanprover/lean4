set_option blast.strategy "cc"
set_option blast.cc.heq true -- make sure heterogeneous congruence lemmas are enabled

example (a b c : Prop) : a = b → b = c → (a ↔ c) :=
by blast

example (a b c : Prop) : a = b → b == c → (a ↔ c) :=
by blast

example (a b c : nat) : a == b → b = c → a == c :=
by blast

example (a b c : nat) : a == b → b = c → a = c :=
by blast

example (a b c d : nat) : a == b → b == c → c == d → a = d :=
by blast

example (a b c d : nat) : a == b → b = c → c == d → a = d :=
by blast

example (a b c : Prop) : a = b → b = c → (a ↔ c) :=
by blast

example (a b c : Prop) : a == b → b = c → (a ↔ c) :=
by blast

example (a b c d : Prop) : a == b → b == c → c == d → (a ↔ d) :=
by blast

definition foo (a b c d : Prop) : a == b → b = c → c == d → (a ↔ d) :=
by blast
