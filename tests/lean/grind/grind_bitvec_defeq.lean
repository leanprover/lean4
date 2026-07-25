import Lean

-- Interpreted values with definitionally equal types must not be treated as distinct.
example (i : BitVec (id 32)) (hne : i ≠ 0#32) : i ≠ 0 := by
  grind
