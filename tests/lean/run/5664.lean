import Std.Tactic.BVDecide

example
  (a k n : BitVec 32) :
  n < -1 - k →
    ((¬a + k + 1 - a ≤ a + k - a ∧ ¬a + k + 1 + n - a ≤ a + k - a) ∧
        ¬a - (a + k + 1) ≤ a + k + 1 + n - (a + k + 1)) ∧
      ¬a + k - (a + k + 1) ≤ a + k + 1 + n - (a + k + 1) := by
  bv_decide
