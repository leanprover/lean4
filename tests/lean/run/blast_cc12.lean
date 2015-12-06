set_option blast.strategy "simple"

definition foo1 (a b : nat) (p : Prop) : a = b → (b = a → p) → p :=
by blast

print foo1

definition foo2 (a b c : nat) (p : Prop) : a = b → b = c → (c = a → p) → p :=
by blast

print foo2

definition foo3 (a b c d : nat) (p : Prop) : a ≠ d → (d ≠ a → p) → p :=
by blast

print foo3

attribute not [reducible]

definition foo4 (a b c d : nat) (p : Prop) : a ≠ d → (d ≠ a → p) → p :=
by blast

attribute ne [semireducible]

definition foo5 (a b c d : nat) (p : Prop) : a ≠ d → (d ≠ a → p) → p :=
by blast

print foo5
