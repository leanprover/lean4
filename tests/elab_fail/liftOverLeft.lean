def foo1 : IO Unit := do
  let f (x : IO.Ref Nat) : IO Nat :=
    pure ((← x.get) + 1)
  IO.println (IO.mkRef 10)

def foo2 : IO Unit := do
  let rec f (x : IO.Ref Nat) : IO Nat :=
    pure ((← x.get) + 1)
  IO.println (IO.mkRef 10)
