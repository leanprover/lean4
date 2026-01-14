def inc : StateM Nat Nat := do
  let s ← get
  modify (· + 1)
  return s

def f (x : Bool) : StateM Nat Nat := do
  let .true := x | return (← inc)
  get

def g (x : Bool) : StateM Nat Nat := do
  let .true := x | do return (← inc)
  get

#eval g true |>.run' 0 -- `0` as expected
#eval f true |>.run' 0 -- should return `0`, not `1`
