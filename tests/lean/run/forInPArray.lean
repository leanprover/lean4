import Std

def check (x : IO Nat) (expected : IO Nat) : IO Unit := do
unless (← x) == (← expected) do
  throw $ IO.userError "unexpected result"

def f1 (xs : Std.PArray Nat) (top : Nat) : IO Nat := do
let mut sum := 0
for x in xs do
  if x % 2 == 0 then
    IO.println s!"x: {x}"
    sum := sum + x
  if sum > top then
    return sum
IO.println s!"sum: {sum}"
return sum

#eval f1 [1, 2, 3, 4, 5, 10, 20].toPersistentArray 10

#eval check (f1 [1, 2, 3, 4, 5, 10, 20].toPersistentArray 10) (pure 16)

def f2 (xs : Std.PArray Nat) (top : Nat) : IO Nat := do
let mut sum := 0
for x in xs do
  if x % 2 == 0 then
    IO.println s!"x: {x}"
    sum := sum + x
  if sum > top then
    break
IO.println s!"sum: {sum}"
return sum

#eval check (f1 (List.iota 100).toPersistentArray 1000) (f2 (List.iota 100).toPersistentArray 1000)
