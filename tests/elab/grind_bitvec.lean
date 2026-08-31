module
open BitVec

example (x : BitVec (w+1)) : (cons x.msb (x.setWidth w)) = x := by
  grind

example {x : BitVec v} (h : w ≤ v) : BitVec.setWidth w (-x) = -BitVec.setWidth w x := by
  grind
