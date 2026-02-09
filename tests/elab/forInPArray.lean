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
info: x: 0
x: 2
x: 4
x: 6
x: 8
x: 10
x: 12
x: 14
x: 16
x: 18
x: 20
x: 22
x: 24
x: 26
x: 28
x: 30
x: 32
x: 34
x: 36
x: 38
x: 40
x: 42
x: 44
x: 46
x: 48
x: 50
x: 52
x: 54
x: 56
x: 58
x: 60
x: 62
x: 64
x: 0
x: 2
x: 4
x: 6
x: 8
x: 10
x: 12
x: 14
x: 16
x: 18
x: 20
x: 22
x: 24
x: 26
x: 28
x: 30
x: 32
x: 34
x: 36
x: 38
x: 40
x: 42
x: 44
x: 46
x: 48
x: 50
x: 52
x: 54
x: 56
x: 58
x: 60
x: 62
x: 64
sum: 1056
-/
#guard_msgs in
#eval check (f1 (List.range 100).toPArray' 1000) (f2 (List.range 100).toPArray' 1000)
