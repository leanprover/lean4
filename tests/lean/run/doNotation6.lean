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
let v ←
  try
    dec x
    return x
  catch _ =>
    return 1

def f2 (xs : List Nat) : M Nat := do
let mut sum := 0
for x in xs do
  try
    dec x
    sum := sum + x
    if sum > 100 then
      break
    continue
  catch _ =>
    break
return sum

/-- info: result 6 -/
#guard_msgs in
#eval testM 100 6 $ f2 [1, 2, 3]

/-- info: result 101 -/
#guard_msgs in
#eval testM 200 101 $ f2 [1, 100, 200, 300]

/-- info: result 1 -/
#guard_msgs in
#eval testM 1 1 $ f2 [1, 100, 200, 300]

def f3 (xs : List Nat) : M Nat := do
let mut sum := 0
for x in xs do
  try
    dec x
    sum := sum + x
    if sum > 100 then
      return sum
    continue
  catch _ =>
    return sum
return sum

/-- info: result 6 -/
#guard_msgs in
#eval testM 100 6 $ f3 [1, 2, 3]

/-- info: result 101 -/
#guard_msgs in
#eval testM 200 101 $ f3 [1, 100, 200, 300]

/-- info: result 1 -/
#guard_msgs in
#eval testM 1 1 $ f3 [1, 100, 200, 300]

def f4 (xs : Array Nat) : IO Nat := do
let mut sum := 0
for x in xs do
  sum := sum + x
  IO.println x
return sum

/--
info: 1
2
3
---
info: 6
-/
#guard_msgs in
#eval f4 #[1, 2, 3]

def f5 (xs : Array Nat) : IO Nat := do
let mut sum := 0
for x in xs[1 : xs.size - 1] do
  sum := sum + x
  IO.println x
return sum

/--
info: 2
3
4
5
---
info: 14
-/
#guard_msgs in
#eval f5 #[1, 2, 3, 4, 5, 6]
