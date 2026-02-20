def foo (x? : Option Nat) : IO Nat := do
  let some x := x? | return 0
  IO.println s!"x: {x}"
  return x

def testFoo (input : Option Nat) (expected : Nat) : IO Unit := do
  assert! (← foo input) == expected

/-- info: x: 10 -/
#guard_msgs in
#eval testFoo (some 10) 10

#guard_msgs in
#eval testFoo none 0

/-- info: x: 1 -/
#guard_msgs in
#eval testFoo (some 1) 1

def bar (x : Nat) : IO (Fin (x + 1)) := do
  let 2 := x | return 0
  -- the pattern match performed a substitution
  let y : Fin 3 := ⟨1, by decide⟩
  return y

def testBar (x : Nat) (expected : Fin (x + 1)) : IO Unit := do
  assert! (← bar x) == expected

#guard_msgs in
#eval testBar 1 0

#guard_msgs in
#eval testBar 2 1

#guard_msgs in
#eval testBar 3 0
