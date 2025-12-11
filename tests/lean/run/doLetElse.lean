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

/-- info: "ok" -/
#guard_msgs in
#eval Id.run do
  let mut x := 0
  let y <- do
    let true := false | do x := x + 3; pure 0 -- NB: this returns from the inner `do` block
    x := x + 100
    return "unreachable"
  if x + y < 23 then pure "ok" else pure "wrong"

/--
error: Type mismatch
  y
has type
  Fin 3
but is expected to have type
  Fin (x + 1)
-/
#guard_msgs in
def bar (x : Nat) : IO (Fin (x + 1)) := do
  let 2 := x | return 0
  -- The pattern match used to perform a substitution in the old `do` elaborator.
  -- However, the feature was unrealiable because it stopped working when there was a join point.
  -- The new `do` elaborator does not support type refinement by `doLetElse` matches.
  let y : Fin 3 := ⟨1, by decide⟩
  return y
