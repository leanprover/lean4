def f1 (x : Nat) : IO Unit :=
  unless x > 10 do
    IO.println s!"x: {x}"

/-- info: x: 0 -/
#guard_msgs in
#eval f1 0

#guard_msgs in
#eval f1 100

def f2 (x : Nat) (ref : IO.Ref Nat) : IO Nat :=
  return x + (←ref.get)

/-- info: 15 -/
#guard_msgs in
#eval id (α := IO Nat) do f2 5 (← IO.mkRef 10)

def f3 (x : Nat) : IO Nat :=
  try
    IO.println x
    throw $ IO.userError "failed"
  catch
    | IO.Error.userError msg => IO.println s!"at catch: {msg}"; pure 0
    | ex => throw ex

/--
info: 5
at catch: failed
---
info: 0
-/
#guard_msgs in
#eval f3 5

def f4 (xs : List Nat) : IO Unit :=
  for x in xs do
    IO.println x

/--
info: 1
2
3
-/
#guard_msgs in
#eval f4 [1,2,3]
