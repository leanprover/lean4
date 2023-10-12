def f (x : Nat) : IO Unit := do
  x -- Error
  IO.println x

def f' (x : Nat) : IO Unit := do
  discard (pure x)
  IO.println x

def g (xs : Array Nat) : IO Unit := do
  xs.set! 0 1 -- Error
  IO.println xs

def g' (xs : Array Nat) : IO Unit := do
  discard <| pure (xs.set! 0 1)
  IO.println xs

def h (xs : Array Nat) : IO Unit := do
  pure (xs.set! 0 1) -- Error
  IO.println xs

def h' (xs : Array Nat) : IO Unit := do
  discard <| pure (xs.set! 0 1)
  IO.println xs

example : IO Unit := do
  let x ← if true then pure true else pure false

example : Id Unit := do
  let mut x ← if true then pure true else pure false
  if let .true := x then
    x := false
