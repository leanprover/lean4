/-! should not parse `case` as a `generalizing` variable -/

example (a b : Nat) : True := by
  induction a generalizing b
  case zero => trivial
  case succ => trivial
