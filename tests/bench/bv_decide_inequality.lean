import Std.Tactic.BVDecide

/-! Smaller real-world problems taken from https://github.com/leanprover/LNSym,
which previously had a bad interaction with the normalization pass -/

variable (a1 a2 b1 b2 a b c d k n : BitVec 64)

example :
  (!decide (b1 - a1 ≤ a2 - a1) && !decide (b2 - a1 ≤ a2 - a1) && !decide (a1 - b1 ≤ b2 - b1) &&
    !decide (a2 - b1 ≤ b2 - b1)) =
  (!decide (a1 - b1 ≤ b2 - b1) && !decide (a2 - b1 ≤ b2 - b1) && !decide (b1 - a1 ≤ a2 - a1) &&
    !decide (b2 - a1 ≤ a2 - a1)) := by
  bv_decide

example :
    a2 - a1 < b1 - a1
    → a2 - a1 < b2 - a1
    → b2 - b1 < a1 - b1
    → b2 - b1 < a2 - b1
    → ¬a1 = b1 := by
  bv_decide

example : ¬a = b ↔ 0#64 < b - a ∧ 0#64 < a - b := by
  bv_decide

example :
    b - a < c - a → b - a < d - a → d - c < a - c → d - c < b - c
    → (0#64 < c - a ∧ 0#64 < d - a) ∧ d - c < a - c := by
  bv_decide

example :
    n < 18446744073709551615#64 - k →
    ((a + k - a < a + k + 1#64 - a ∧ a + k - a < a + k + 1#64 + n - a) ∧
        a + k + 1#64 + n - (a + k + 1#64) < a - (a + k + 1#64)) ∧
      a + k + 1#64 + n - (a + k + 1#64) < a + k - (a + k + 1#64) := by
  bv_decide (config := { timeout := 120 })

example :
    n < 18446744073709551615 →
    (0#64 < addr + 1#64 - addr ∧ 0#64 < addr + 1#64 + n - addr)
    ∧ addr + 1#64 + n - (addr + 1#64) < addr - (addr + 1#64) := by
  bv_decide

example :
    a2 - a1 < b1 - a1 → a2 - a1 < b2 - a1 →
    b2 - b1 < a1 - b1 → b2 - b1 < a2 - b1 →
    b2 - b1 = 18446744073709551615#64 ∨ c2 - b1 ≤ b2 - b1 ∧ c1 - b1 ≤ c2 - b1 →
    ((a2 - a1 < c1 - a1 ∧ a2 - a1 < c2 - a1)
    ∧ c2 - c1 < a1 - c1)
    ∧ c2 - c1 < a2 - c1 := by
  bv_decide (config := { timeout := 120 })
