/-! Tests import error messages for bv_decide -/


/-- error: to use `bv_decide`, please include `import Std.Tactic.BVDecide` -/
#guard_msgs in
example (x : BitVec 8) : x - 1 + 1 = x := by
  bv_decide

/-- error: to use `bv_decide`, please include `import Std.Tactic.BVDecide` -/
#guard_msgs in
example (x : BitVec 8) : x - 1 + 1 = x := by
  sym =>
    bv_decide
