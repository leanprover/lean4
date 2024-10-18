import Lean.Data.PersistentArray

def check (x : IO Nat) (expected : IO Nat) : IO Unit := do
unless (← x) == (← expected) do
  throw $ IO.userError "unexpected result"

def f1 (xs : Lean.PArray Nat) (top : Nat) : IO Nat := do
let mut sum := 0
for x in xs do
  if x % 2 == 0 then
    IO.println s!"x: {x}"
    sum := sum + x
  if sum > top then
    return sum
IO.println s!"sum: {sum}"
return sum

/--
info: x: 2
x: 4
x: 10
---
info: 16
-/
#guard_msgs in
#eval f1 [1, 2, 3, 4, 5, 10, 20].toPArray' 10

/--
info: x: 2
x: 4
x: 10
-/
#guard_msgs in
#eval check (f1 [1, 2, 3, 4, 5, 10, 20].toPArray' 10) (pure 16)

def f2 (xs : Lean.PArray Nat) (top : Nat) : IO Nat := do
let mut sum := 0
for x in xs do
  if x % 2 == 0 then
    IO.println s!"x: {x}"
    sum := sum + x
  if sum > top then
    break
IO.println s!"sum: {sum}"
return sum

/--
info: x: 100
x: 98
x: 96
x: 94
x: 92
x: 90
x: 88
x: 86
x: 84
x: 82
x: 80
x: 78
x: 100
x: 98
x: 96
x: 94
x: 92
x: 90
x: 88
x: 86
x: 84
x: 82
x: 80
x: 78
sum: 1068
-/
#guard_msgs in
#eval check (f1 (List.iota 100).toPArray' 1000) (f2 (List.iota 100).toPArray' 1000)
