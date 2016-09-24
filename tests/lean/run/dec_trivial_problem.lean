
definition n : nat := 3

open tactic
meta definition dec_triv : tactic unit :=
do tgt  ← target,
   inst ← to_expr `(decidable %%tgt) >>= mk_instance,
   to_expr `(@of_as_true %%tgt %%inst trivial) >>= exact

example : 0 < n :=
by dec_triv

notation `dec_trivial2` := by dec_triv

example : 0 < n :=
dec_trivial2

notation `dec_trivial3` := of_as_true (by triv)

example : 0 < n :=
dec_trivial3
