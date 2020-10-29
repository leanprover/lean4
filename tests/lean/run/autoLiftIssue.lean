def g (x : Nat) : IO Nat := do
  IO.println x
  pure x

def f {m} [MonadLiftT IO m] : m Nat :=
  g 10
