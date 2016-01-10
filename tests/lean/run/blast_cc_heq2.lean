set_option blast.strategy "cc"
set_option blast.cc.heq true -- make sure heterogeneous congruence lemmas are enabled

example (a b c : nat) (f : nat → nat) : a == b → b = c → f a == f c :=
by blast

example (a b c : nat) (f : nat → nat) : a == b → b = c → f a = f c :=
by blast

example (a b c d : nat) (f : nat → nat) : a == b → b = c → c == f d → f a = f (f d) :=
by blast
