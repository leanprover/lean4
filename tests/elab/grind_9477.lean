module

inductive BoundShape where
  | «open» : BoundShape
  | closed : BoundShape
  | unbounded : BoundShape

structure RangeShape where
  lower : BoundShape
  upper : BoundShape

abbrev Bound (shape : BoundShape) (α : Type u) : Type u :=
  match shape with
  | .open | .closed => α
  | .unbounded => PUnit

structure PRange {shape : RangeShape} (α : Type u) where
  lower : Bound shape.lower α
  upper : Bound shape.upper α

structure T where
  upper_bound : Nat

def T.range (a : T) := PRange.mk (shape := ⟨.closed, .open⟩) 0 a.upper_bound

theorem range_lower (a : T) : a.range.lower = 0 := by rfl

/--
info: range_lower (a : T) :
  @Eq (Bound { lower := BoundShape.closed, upper := BoundShape.open }.lower Nat)
    (@PRange.lower { lower := BoundShape.closed, upper := BoundShape.open } Nat a.range)
    (@OfNat.ofNat (Bound { lower := BoundShape.closed, upper := BoundShape.open }.lower Nat) (nat_lit 0)
      (instOfNatNat (nat_lit 0)))
-/
#guard_msgs in
set_option pp.explicit true in
#check range_lower

set_option warn.sorry false

#guard_msgs in
theorem test (p : T) (n: Nat) : n ≤ p.range.upper := by
  fail_if_success grind only [range_lower]
  sorry

example (p : T) (n: Nat) : n ≥ p.range.lower := by
  set_option trace.Meta.debug true in
  grind only [range_lower]
