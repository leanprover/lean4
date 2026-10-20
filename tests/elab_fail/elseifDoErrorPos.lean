def f (x : Nat) : IO Nat := do
  if x == 0 then
    return 0
  else if x then
    return 1
  else
    return "a"
