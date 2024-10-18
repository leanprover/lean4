def f (x : Nat) : IO Nat := do
IO.println "hello world"
let aux (y : Nat) (z : Nat) : IO Nat := do
  IO.println "aux started"
  IO.println s!"y: {y}, z: {z}"
  pure (x+y)
discard <| aux x
  (x + 1) -- It is part of the application since it is indented
discard <| aux x (x -- parentheses use `withoutPosition`
-1)
discard <| aux x x;
  aux x
 x

/--
info: hello world
aux started
y: 10, z: 11
aux started
y: 10, z: 9
aux started
y: 10, z: 10
aux started
y: 10, z: 10
---
info: 20
-/
#guard_msgs in
#eval f 10

def g (xs : List Nat) : StateT Nat Id Nat := do
let mut xs := xs
if xs.isEmpty then
  xs := [← get]
dbg_trace ">>> xs: {xs}"
return xs.length

/--
info: >>> xs: [1, 2, 3]
---
info: 3
-/
#guard_msgs in
#eval g [1, 2, 3] |>.run' 10

/--
info: >>> xs: [10]
---
info: 1
-/
#guard_msgs in
#eval g [] |>.run' 10

theorem ex1 : (g [1, 2, 4, 5] |>.run' 0) = 4 :=
rfl

theorem ex2 : (g [] |>.run' 0) = 1 :=
rfl

def h (x : Nat) (y : Nat) : Nat := Id.run <| do
let mut x := x
let mut y := y
if x > 0 then
  let y' := x + 1
  x := y'
else
  y := y + 1
return x + y

theorem ex3 (y : Nat) : h 0 y = 0 + (y + 1) :=
rfl

theorem ex4 (y : Nat) : h 1 y = (1 + 1) + y :=
rfl

def sumOdd (xs : List Nat) (threshold : Nat) : Nat := Id.run <| do
let mut sum := 0
for x in xs do
  if x % 2 == 1 then
    sum := sum + x
  if sum > threshold then
    break
  unless x % 2 == 1 do
    continue
  dbg_trace ">> x: {x}"
return sum

/--
info: >> x: 1
>> x: 3
>> x: 5
---
info: 16
-/
#guard_msgs in
#eval sumOdd [1, 2, 3, 4, 5, 6, 7, 9, 11, 101] 10

theorem ex5 : sumOdd [1, 2, 3, 4, 5, 6, 7, 9, 11, 101] 10 = 16 :=
rfl

-- We need `Id.run` because we still have `Monad Option`
def find? (xs : List Nat) (p : Nat → Bool) : Option Nat := Id.run do
let mut result := none
for x in xs do
  if p x then
    result := x
    break
return result

def sumDiff (ps : List (Nat × Nat)) : Nat := Id.run do
let mut sum := 0
for (x, y) in ps do
  sum := sum + x - y
return sum

theorem ex7 : sumDiff [(2, 1), (10, 5)] = 6 :=
rfl

def f1 (x : Nat) : IO Unit := do
let rec loop : Nat → IO Unit
  | 0   => pure ()
  | x+1 => do IO.println x; loop x
loop x

/--
info: 9
8
7
6
5
4
3
2
1
0
-/
#guard_msgs in
#eval f1 10

partial def f2 (x : Nat) : IO Unit := do
let rec
  isEven : Nat → Bool
    | 0   => true
    | x+1 => isOdd x,
  isOdd : Nat → Bool
    | 0   => false
    | x+1 => isEven x
IO.println ("isOdd(" ++ toString x ++ "): " ++ toString (isOdd x))

/-- info: isOdd(11): true -/
#guard_msgs in
#eval f2 11

/-- info: isOdd(10): false -/
#guard_msgs in
#eval f2 10

def split (xs : List Nat) : List Nat × List Nat := Id.run do
let mut evens := []
let mut odds  := []
for x in xs.reverse do
  if x % 2 == 0 then
    evens := x :: evens
  else
    odds := x :: odds
return (evens, odds)

theorem ex8 : split [1, 2, 3, 4] = ([2, 4], [1, 3]) :=
rfl

def f3 (x : Nat) : IO Bool := do
let y ← cond (x == 0) (do IO.println "hello"; pure true) (pure false);
pure !y

def f4 (x y : Nat) : Nat × Nat := Id.run <| do
  let mut (x, y) := (x, y)
  match x with
  | 0 => y := y + 1
  | _ => x := x + y
  return (x, y)

#guard f4 0 10 == (0, 11)
#guard f4 5 10 == (15,10)

theorem ex9 (y : Nat) : f4 0 y = (0, y+1) :=
rfl

theorem ex10 (x y : Nat) : f4 (x+1) y = ((x+1)+y, y) :=
rfl

def f5 (x y : Nat) : Nat × Nat := Id.run <| do
  let mut (x, y) := (x, y)
  match x with
  | 0   => y := y + 1
  | z+1 => dbg_trace "z: {z}"; x := x + y
  return (x, y)

/--
info: z: 4
---
info: (11, 6)
-/
#guard_msgs in
#eval f5 5 6

theorem ex11 (x y : Nat) : f5 (x+1) y = ((x+1)+y, y) :=
rfl

def f6 (x : Nat) : Nat := Id.run <| do
  let mut x := x
  if x > 10 then
    return 0
  x := x + 1
  return x

theorem ex12 : f6 11 = 0 :=
rfl

theorem ex13 : f6 5 = 6 :=
rfl

def findOdd (xs : List Nat) : Nat := Id.run <| do
for x in xs do
  if x % 2 == 1 then
    return x
return 0

theorem ex14 : findOdd [2, 4, 5, 8, 7] = 5 :=
rfl

theorem ex15 : findOdd [2, 4, 8, 10] = 0 :=
rfl

def f7 (ref : IO.Ref (Option (Nat × Nat))) : IO Nat := do
let some (x, y) ← ref.get | pure 100
IO.println (toString x ++ ", " ++ toString y)
return x+y

def f7Test : IO Unit := do
unless (← f7 (← IO.mkRef (some (10, 20)))) == 30 do throw $ IO.userError "unexpected"
unless (← f7 (← IO.mkRef none)) == 100 do throw $ IO.userError "unexpected"

/-- info: 10, 20 -/
#guard_msgs in
#eval f7Test

def f8 (x : Nat) : IO Nat := do
let y ←
  if x == 0 then
    IO.println "x is zero"
    return 100 --  returns from the `do`-block
  else
    pure (x + 1)
IO.println ("y: " ++ toString y)
return y

def f8Test : IO Unit := do
unless (← f8 0) == 100 do throw $ IO.userError "unexpected"
unless (← f8 1) == 2 do throw $ IO.userError "unexpected"

/--
info: x is zero
y: 2
-/
#guard_msgs in
#eval f8Test
