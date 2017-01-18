open tactic

meta def f (n : nat) : tactic unit :=
trace "hello" >>
trace "------------" >>
trace_call_stack

meta def g (n : nat) : tactic unit :=
trace "world" >> f n

run_command (do
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  x ← return 5,
  g 1)
