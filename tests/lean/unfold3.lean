import data.nat
open nat tactic

definition fib : nat → nat
| 0        := 1
| 1        := 1
| (n+2)    := fib n + fib (n+1)

example (a : nat) : fib a > 0 :=
by do
  get_local "a" >>= λ H, induction_core semireducible H ("nat" <.> "rec_on") ["n", "iH1"],
  trace_state, trace "-------",
  unfold ["fib"],
  trace_state, trace "-------",
  mk_const "zero_lt_one" >>= apply,
  trace_state, trace "-------",
  get_local "n" >>= cases,
  unfold ["fib"],
  mk_const "zero_lt_one" >>= apply,
  unfold ["fib"],
  trace_state,
  mk_const "add_pos_of_nonneg_of_pos" >>= apply,
  mk_const ("nat" <.> "zero_le") >>= apply,
  assumption
