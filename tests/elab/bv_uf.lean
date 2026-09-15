import Std.Tactic.BVDecide


set_option trace.Meta.Tactic.bv true in
example (f g : BitVec 8 → BitVec 8) (x y : BitVec 8) (h : x = y) :
    f (g x) = f (g y) := by
  bv_decide

set_option trace.Meta.Tactic.bv true in
example (f g : BitVec 8 → BitVec 8) (x y : BitVec 8) (h : x = y) :
    f (g (if x = 0 then 0 else f x)) = f (g y) := by
  bv_decide

