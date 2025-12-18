
@[noinline] def f (a : Nat × Nat × Nat) : Nat:=
  a.fst + a.snd.fst + a.snd.snd

def main : IO Unit := do
  IO.println (f (1, 2, 3,))
