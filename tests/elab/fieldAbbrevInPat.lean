structure A where
  x : Nat
  y : Nat

def f (a : A) : Nat :=
  let {x, y} := a
  x + y
