constant p : nat → Prop
open tactic
set_option pp.all true

definition ex (a b c : nat) (H : p c) : a = b → p a → p b :=
by do intro "H1", intro "H2",
      subst "a",
      trace_state,
      assumption

print ex

example (a b c : nat) (H : p c) : a = b → p a → p b :=
by do intros,
      subst "b",
      trace_state,
      assumption
