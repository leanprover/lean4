set_option blast.subst false
set_option blast.simp false
set_option pp.all true

definition foo1 (a b : nat) (p : Prop) : a = b → (b = a → p) → p :=
by blast

print foo1

definition foo2 (a b c : nat) (p : Prop) : a = b → b = c → (c = a → p) → p :=
by blast

print foo2

definition foo3 (a b c d : nat) (p : Prop) : a ≠ d → (d ≠ a → p) → p :=
by blast

print foo3
