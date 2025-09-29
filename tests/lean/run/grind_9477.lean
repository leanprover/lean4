module
structure T where
  upper_bound : Nat

def T.range (a : T) := 0...a.upper_bound

theorem range_lower (a : T) : a.range.lower = 0 := by rfl

/--
info: range_lower (a : T) :
  @Eq (Std.PRange.Bound { lower := Std.PRange.BoundShape.closed, upper := Std.PRange.BoundShape.open }.lower Nat)
    (@Std.PRange.lower { lower := Std.PRange.BoundShape.closed, upper := Std.PRange.BoundShape.open } Nat a.range)
    (@OfNat.ofNat
      (Std.PRange.Bound { lower := Std.PRange.BoundShape.closed, upper := Std.PRange.BoundShape.open }.lower Nat)
      (nat_lit 0) (instOfNatNat (nat_lit 0)))
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
