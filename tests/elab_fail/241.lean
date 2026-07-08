def ex1 : IO Unit := do
  let mut xs : Array Nat := #[]
  let xs := xs -- Error
  xs := xs.push 0
  IO.println xs

def ex2 : IO Unit := do
  let mut xs : Array Nat := #[]
  let (xs, _) := (xs, 4) -- Error
  xs := xs.push 0
  IO.println xs

def ex3 : IO Unit := do
  let mut xs : Array Nat := #[]
  match (1, 2) with
  | (xs, ys) => -- Error
    xs := xs.push 0
    IO.println xs

def ex4 : IO Unit := do
  let mut xs : Array Nat := #[]
  let (xs, _) ← pure (xs, 4) -- Error
  xs := xs.push 0
  IO.println xs

def ex5 : IO Unit := do
  let mut xs : Array Nat := #[]
  let xs ← pure xs -- Error
  xs := xs.push 0
  IO.println xs

def ex6 : IO Unit := do
  let mut xs : Array Nat := #[]
  if let some xs ← pure (some 4) then -- Error
    IO.println xs
  else
    pure ()

def ex7 : IO Unit := do
  let mut xs : Array Nat := #[]
  if let some xs := some 4 then -- Error
    IO.println xs
  else
    pure ()

def ex8 : IO Unit := do
  let mut xs : Array Nat := #[]
  if let some xs ← pure (some 4) then -- Error
    IO.println xs
  else
    pure ()

def ex9 : IO Unit := do
  let mut xs : Array Nat := #[]
  try
    IO.println xs
  catch
    | IO.Error.userError xs => -- Error
      pure ()
    | _ =>
      pure ()

def ex10 : IO Unit := do
  let mut xs : Array Nat := #[]
  try
    IO.println xs
  catch xs => -- Error
    pure ()

def ex11 : IO Unit := do
  let mut xs : Array (Nat × Nat) := #[(1,2)]
  for (xs, y) in xs do -- Error
    xs := xs.push (0, 0)
    IO.println xs

def ex12 : IO Unit := do
  let mut xs : Array Nat := #[1,2,3]
  for xs in xs do -- Error
    xs := xs.push 0
    IO.println xs

def ex13 : IO Unit := do
  let mut xs : Array Nat := #[1,2,3]
  for a in [:10], xs in [1,2,3] do -- Error
    xs := xs.push 0
    IO.println xs
