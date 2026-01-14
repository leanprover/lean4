open BitVec

example (x : BitVec n) : zeroExtend (if 1#1 = 1#1 then 128 else 64) x = zeroExtend 128 x := by
  simp

example (x : BitVec n) : zeroExtend (if 1#1 = 0#1 then 128 else 64) x = zeroExtend 64 x := by
  simp

abbrev f (_ : 1#1 = 1#1) := 128

example (h' : 128 = n) : (if h : 1#1 = 1#1 then f h else 20) = n := by
  dsimp [-dite_eq_ite]
  guard_target = f _ = n
  exact h'

abbrev g (_ : 1#1 ≠ 0#1) := 128

example (h' : 128 = m) : (if h : 1#1 = 0#1 then 10 else g h) = m := by
  dsimp [-dite_eq_ite]
  guard_target = g _ = m
  exact h'
