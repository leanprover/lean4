set_option blast.subst false
set_option blast.simp  false

definition t1 (a b : nat) : (a = b ↔ a = b) :=
by blast

print t1
