attribute [grind? =] BitVec.sdiv_zero

example {x : BitVec 32} : x.sdiv 0#32 = 0#32 := by
  grind

example {x : BitVec 32} : x.sdiv 0#32 = 0#32 := by
  grind -ext
