set_option blast.subst false
set_option blast.simp false

definition foo1 (a b : nat) (p : Prop) : a = b → (b = a → p) → p :=
by blast

print foo1

definition foo2 (a b c : nat) (p : Prop) : a = b → b = c → (c = a → p) → p :=
by blast

print foo2
