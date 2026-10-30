/-!
Tests that the term after `return` can start on a later line if it is indented past the `return`
keyword, and that a bare `return` does not take the next statement as its argument.
See also `returnOptIssue.lean`.
-/

def nextLine (x : Nat) : Id Nat := do
  if x = 0 then
    return
      x + 5
  return x

#guard (nextLine 0).run == 5
#guard (nextLine 3).run == 3

def multiLine (x : Nat) : Id (List Nat) := do
  return
    [x,
     x + 1]

#guard (multiLine 1).run == [1, 2]

/-! Continuation lines of the argument only need to be indented past `return`. -/

def continuation (x : Nat) : Id Nat := do
  return
    Nat.add
    x
    1

#guard (continuation 1).run == 2

def termLevel : Id Nat :=
  return
    7

#guard termLevel.run == 7

/-! A statement at the column of `return` is the next statement, not the argument. -/

def sameColumn : IO Unit := do
  for i in [1, 2] do
    if i = 2 then
      return
    IO.println s!"i = {i}"

/-- info: i = 1 -/
#guard_msgs in
#eval sameColumn

/-! A line to the left of a `return` in the middle of a line is the next statement. -/

def midLine (x : Nat) : IO Unit := do
  if x = 0 then return
    IO.println "after if"

/-- info: after if -/
#guard_msgs in
#eval midLine 1

#guard_msgs in
#eval midLine 0

def matchArms (x : Nat) : IO Unit := do
  match x with
  | 0 => return
  | _ => IO.println "nonzero"

/-- info: nonzero -/
#guard_msgs in
#eval matchArms 3
