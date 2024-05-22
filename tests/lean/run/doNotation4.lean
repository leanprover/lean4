abbrev M := StateRefT Nat IO

def testM {α} [ToString α] [BEq α] (init : Nat) (expected : α) (x : M α): IO Unit := do
let v ← x.run' init
IO.println ("result " ++ toString v)
unless v == expected do
  throw $ IO.userError "unexpected"

def dec (x : Nat) : M Unit := do
if (← get) == 0 then
  throw $ IO.userError "value is zero"
modify (· - x)

def f1 (x : Nat) : M Nat := do
try
  dec x
  dec x
  get
catch _ =>
  pure 1000
finally
  IO.println "done"

/--
info: done
result 8
-/
#guard_msgs in
#eval testM 10 8 $ f1 1

/--
info: done
result 1000
-/
#guard_msgs in
#eval testM 1 1000 $ f1 1

def f2 (x : Nat) : M Nat := do
try
  if x > 100 then
    return x
  dec x
  pure (← get)
catch _ =>
  pure 1000
finally
  IO.println "done"

/--
info: done
result 500
-/
#guard_msgs in
#eval testM 0 500 $ f2 500

/--
info: done
result 1000
-/
#guard_msgs in
#eval testM 0 1000 $ f2 50

/--
info: done
result 150
-/
#guard_msgs in
#eval testM 200 150 $ f2 50

def f3 (x : Nat) : M Nat := do
try
  dec x
  pure (← get)
catch
  | IO.Error.userError err => IO.println err; pure 2000
  | ex => throw ex

/--
info: value is zero
result 2000
-/
#guard_msgs in
#eval testM 0 2000 $ f3 10

def f4 (xs : List Nat) : M Nat := do
let mut y := 0
for x in xs do
  IO.println s!"x: {x}"
  try
    dec x
    y := y + x
  catch _ =>
    set y
    break
get

/--
info: x: 1
x: 2
x: 3
x: 4
result 6
-/
#guard_msgs in
#eval testM 5 6 $ f4 [1, 2, 3, 4, 5, 6]

/--
info: x: 1
x: 2
x: 3
x: 4
x: 5
x: 6
result 19
-/
#guard_msgs in
#eval testM 40 19 $ f4 [1, 2, 3, 4, 5, 6]

def f5 (xs : List Nat) : M Nat := do
let mut y := 0
for x in xs do
  IO.println s!"x: {x}"
  try
    dec x
    y := y + x
  catch _ =>
    return y
IO.println "after for"
modify (· - 1)
get

/--
info: x: 1
x: 2
x: 3
x: 4
result 6
-/
#guard_msgs in
#eval testM 5 6 $ f5 [1, 2, 3, 4, 5, 6]

/--
info: x: 1
x: 2
x: 3
x: 4
x: 5
x: 6
after for
result 18
-/
#guard_msgs in
#eval testM 40 18 $ f5 [1, 2, 3, 4, 5, 6]
