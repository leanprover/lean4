/-!
Testing delaboration of `letFun` as a `doElem`
-/

/-!
A `have` in the middle of a `do` expression.
-/
def x : IO Nat := do
  println! "a"
  have a := 1
  println! "b"
  return a

#print x
