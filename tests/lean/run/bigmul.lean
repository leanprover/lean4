

@[noinline] def f (x : Nat) :=
1000000000000000000000000000000

@[noinline] def tst1 (n : Nat) : IO Unit := do
IO.println (n * f n)

@[noinline] def tst2 (n : Nat) : IO Unit := do
IO.println (f n * n)

#eval tst1 0
#eval tst2 0
