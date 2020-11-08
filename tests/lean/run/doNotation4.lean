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

#eval testM 10 8 $ f1 1
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

#eval testM 0 500 $ f2 500
#eval testM 0 1000 $ f2 50
#eval testM 200 150 $ f2 50

def f3 (x : Nat) : M Nat := do
try
  dec x
  pure (← get)
catch
  | IO.Error.userError err => IO.println err; pure 2000
  | ex => throw ex

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

#eval testM 5 6 $ f4 [1, 2, 3, 4, 5, 6]
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

#eval testM 5 6 $ f5 [1, 2, 3, 4, 5, 6]
#eval testM 40 18 $ f5 [1, 2, 3, 4, 5, 6]
