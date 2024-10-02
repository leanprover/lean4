import Std.Tactic.BVDecide

theorem x_eq_y (x y : Bool) (hx : x = True) (hy : y = True) : x = y := by
  bv_decide

example (z : BitVec 64) : True := by
  let x : BitVec 64 := 10
  let y : BitVec 64 := 20 + z
  have : z + (2 * x) = y := by
    bv_decide
  exact True.intro

example :
  ¬ (0 ≤ 0 + 16#64 ∧ 0 ≤ 0 + 16#64 ∧ (0 + 16#64 ≤ 0 ∨ 0 ≥ 0 + 16#64 ∨ 16#64 = 0 ∨ 16#64 = 0)) := by
  bv_normalize

example (x y z : BitVec 8) (h1 : x = z → False) (h2 : x = y) (h3 : y = z) : False := by
  bv_decide
