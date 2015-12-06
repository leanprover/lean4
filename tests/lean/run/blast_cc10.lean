set_option blast.strategy "cc"

definition t1 (a b : nat) : (a = b ↔ a = b) :=
by blast

print t1
