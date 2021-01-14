def f : IO Nat := do
  IO.println "hello"
  IO.getStdin
  return 10

def f1 : ExceptT String (StateT Nat Id) Nat := do
  modify (· + 1)
  get

def f2 (x : Nat) : ExceptT String (StateT Nat Id) Nat := do
  modify (· + x)
  get

def g1 : ExceptT String (StateT Nat Id) Unit := do
  let x : String ← f1
  return ()

def g2 : ExceptT String (StateT Nat Id) Unit := do
  let x : String ← f2 10
  return ()

def g3 : ExceptT String (StateT Nat Id) String := do
  let x ← f2
  f1
