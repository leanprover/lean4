import Std.Tactic.BVDecide

theorem x_eq_y (x y : Bool) (hx : x = True) (hy : y = True) : x = y := by
  bv_decide
