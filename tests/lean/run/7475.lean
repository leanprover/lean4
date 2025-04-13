import Std.Tactic.BVDecide

inductive Sign : Type
| Positive : Sign
| Negative : Sign
deriving DecidableEq, Repr

inductive EFixedPoint : Type
| NaN : EFixedPoint
| Infinity : Sign -> EFixedPoint
deriving DecidableEq, Repr

namespace EFixedPoint

def equal (a b : EFixedPoint) : Bool :=
  match a, b with
  | Infinity s1, Infinity s2 => s1 = s2
  | _, _ => false

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem EFixedPoint_eq_refl (a : EFixedPoint) : a.equal a = true := by
  unfold EFixedPoint.equal
  bv_normalize
  sorry

end EFixedPoint
