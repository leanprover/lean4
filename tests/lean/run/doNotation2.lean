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
