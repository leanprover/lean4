def foo (x? : Option Nat) : IO Nat := do
  let some x := x? | return 0
  IO.println s!"x: {x}"
  return x

def test (input : Option Nat) (expected : Nat) : IO Unit := do
  assert! (← foo input) == expected


#eval test (some 10) 10
#eval test none 0
#eval test (some 1) 1
