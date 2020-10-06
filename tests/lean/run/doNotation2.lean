new_frontend

def f (x : Nat) : IO Nat := do
IO.println "hello world"
let aux (y : Nat) (z : Nat) : IO Nat := do
  IO.println "aux started"
  IO.println ("y: " ++ toString y ++ ", z: " ++ toString z)
  pure (x+y)
aux x
  (x + 1) -- It is part of the application since it is indented
aux x (x -- parentheses use `withoutPosition`
-1)
aux x x;
  aux x
 x

#eval f 10

def g (xs : List Nat) : StateT Nat Id Nat := do
if xs.isEmpty then
  xs := [← get]
dbgTrace! ">>> xs: " ++ toString xs
return xs.length

#eval g [1, 2, 3] $.run' 10
#eval g [] $.run' 10

theorem ex1 : (g [1, 2, 4, 5] $.run' 0) = 4 :=
rfl

theorem ex2 : (g [] $.run' 0) = 1 :=
rfl

def h (x : Nat) (y : Nat) : Nat := do
if x > 0 then
  let y := x + 1 -- this is a new `y` that shadows the one above
  x := y
else
  y := y + 1
return x + y

theorem ex3 (y : Nat) : h 0 y = 0 + (y + 1) :=
rfl

theorem ex4 (y : Nat) : h 1 y = (1 + 1) + y :=
rfl

def sumOdd (xs : List Nat) (threshold : Nat) : Nat := do
let sum := 0
for x in xs do
  if x % 2 == 1 then
    sum := sum + x
  if sum > threshold then
    break
  unless x % 2 == 1 do
    continue
  dbgTrace! ">> x: " ++ toString x
return sum

#eval sumOdd [1, 2, 3, 4, 5, 6, 7, 9, 11, 101] 10

theorem ex5 : sumOdd [1, 2, 3, 4, 5, 6, 7, 9, 11, 101] 10 = 16 :=
rfl

def mapOdd (f : Nat → Nat) (xs : List Nat) : List Nat := do
for x in xs do
  if x % 2 == 1 then
    x := f x
  dbgTrace! ">> mapOdd x: " ++ toString x

#eval mapOdd (·+10) [1, 2, 3, 4, 5, 6, 7, 9]

theorem ex6 : mapOdd (·+10) [1, 2, 3, 4, 5, 6, 7, 9] = [11, 2, 13, 4, 15, 6, 17, 19] :=
rfl

-- We need `Id.run` because we still have `Monad Option`
def find? (xs : List Nat) (p : Nat → Bool) : Option Nat := Id.run do
let result := none
for x in xs do
  if p x then
    result := x
    break
return result

def sumDiff (ps : List (Nat × Nat)) : Nat := do
let sum := 0
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

#eval f2 11
#eval f2 10

def split (xs : List Nat) : List Nat × List Nat := do
let evens := []
let odds  := []
for x in xs.reverse do
  if x % 2 == 0 then
    evens := x :: evens
  else
    odds := x :: odds
return (evens, odds)

theorem ex8 : split [1, 2, 3, 4] = ([2, 4], [1, 3]) :=
rfl
