def f1 (x : Nat) : IO Unit := do
  IO.println x
  return ()

def g1 : IO Unit := do
  f1 -- Error
  pure ()

def f2 (x : Nat) (y : Nat) : IO Unit := do
  IO.println s!"{x} {y}"
  return ()

def g2 : IO Unit := do
  f2 10 -- Error
  pure ()
