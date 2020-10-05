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
