

@[noinline] def f (x : Nat) :=
1000000000000000000000000000000

@[noinline] def tst1 (n : Nat) : IO Unit := do
IO.println (n * f n)

@[noinline] def tst2 (n : Nat) : IO Unit := do
IO.println (f n * n)

/-- info: 0 -/
#guard_msgs in
#eval tst1 0

/-- info: 0 -/
#guard_msgs in
#eval tst2 0
