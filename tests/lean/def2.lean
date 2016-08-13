set_option new_elaborator true

axiom val : nat

definition foo : nat :=
val

noncomputable definition foo : nat :=
val

noncomputable definition bla : nat :=
2
