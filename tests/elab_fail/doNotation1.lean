--

def f1 (x : Nat) : IO Nat := do
y := 1  -- error 'y' cannot be reassigned

def f2 (xs : List (Nat × Nat)) : Unit := Id.run <| do
for (x, y) in xs do
  (y, x) := (x, y) -- error 'y' (and 'x') cannot be reassigned

def f3 (xs : List (Nat × Nat)) : Unit := Id.run <| do
for p in xs do
  p := (p.2, p.1) -- works. `forInMap` requires a variable

inductive Vector' (α : Type) : Nat → Type
| nil  : Vector' α 0
| cons : α → {n : Nat} → Vector' α n → Vector' α (n+1)
def f4 (b : Bool) (n : Nat) (v : Vector' Nat n) : Vector' Nat (n+1) := Id.run <| do
let mut v := v
if b then
  v := Vector'.cons 1 v
Vector'.cons 1 v
def f5 (y : Nat) (xs : List Nat) : List Bool := Id.run <| do
let mut y := y
for x in xs do
  y := true -- invalid reassigned
return []

def f6 (xs : List Nat) : IO (List Nat) := do
for x in xs do -- type error
  IO.println x
return []

def f7 (xs : List Nat) : IO Unit := do
unless xs.isEmpty do
  break -- error must be inside 'for'

def f8 (xs : List Nat) : IO Unit := do
unless xs.isEmpty do
  continue -- error must be inside 'for'

def f9 (xs : List Nat) : IO (List Nat) := do
return xs
return xs -- warn unreachable

def f10 (x : Nat) : IO Unit := do
IO.println x

#print f10 -- we do not generate an unnecessary bind

def f11 (x : Nat) : IO Unit := do
if x > 0 then
  IO.println "x is not zero"
IO.mkRef true -- error here as expected
def f12 (x : Nat) : IO Bool := do
let mut x := x
if x > 0 then
  pure true -- error here; the expected type is `IO Unit` because the `if` is non-terminal
else
  x := x + 1
  IO.println "hello"
if x > 0 then
  pure true
else
  x := x + 1
  IO.println "hello" -- error here; the expected type is `IO Bool`

def f13 (xs : List Nat) : IO Bool := do
if xs == [] then
  return true
else
  return false
IO.println "hello" -- warn unreachable
return false

def f14 (x : Nat) : IO Nat := do
let y ← if x == 0 then return 100 else return 200
IO.println ("y: " ++ toString y) -- warn unreachable
return 0

example (xs : List (Nat × Nat)) : List (Nat × Nat) := Id.run <| do
for _ in xs do -- error, `for` result type is PUnit but expected type is List (Nat × Nat)
  pure ()
