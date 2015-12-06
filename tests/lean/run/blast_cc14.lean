set_option blast.strategy "cc"

constant R : nat → nat → Prop
axiom R_trans : ∀ a b c, R a b → R b c → R a c
attribute R_trans [trans]

set_option blast.subst false

example (a b c : nat) : a = b → R a b → R a a :=
by blast
