/-!
# Tests for delaborators for Std.Range and Std.PRange
-/

/-!
## Tests for `Std.Range`
-/

/-!
Default lower bound and step
-/
/-- info: [:10] : Std.Range -/
#guard_msgs in #check Std.Range.mk 0 10 1 (by grind)

/-!
Default step
-/
/-- info: [5:10] : Std.Range -/
#guard_msgs in #check Std.Range.mk 5 10 1 (by grind)

/-!
Default lower bound
-/
/-- info: [:10:2] : Std.Range -/
#guard_msgs in #check Std.Range.mk 0 10 2 (by grind)

/-!
No defaults
-/
/-- info: [5:10:2] : Std.Range -/
#guard_msgs in #check Std.Range.mk 5 10 2 (by grind)

/-!
Disable notation
-/
/-- info: { stop := 10, step_pos := _check._proof_1 } : Std.Range -/
#guard_msgs in set_option pp.notation false in #check Std.Range.mk 0 10 1 (by grind)

/-!
## Tests for `Std.PRange`
-/

/-!
Each of the possibilities, in order of appearance in `Lean.PrettyPrinter.Delaborator.delabPRange`.
-/
/-- info: 1...=10 : Std.Rcc Nat -/
#guard_msgs in #check 1...=10
/-- info: *...=10 : Std.Ric Nat -/
#guard_msgs in #check *...=10
/-- info: 1...* : Std.Rci Nat -/
#guard_msgs in #check 1...*
/-- info: *...* : Std.Rii Nat -/
#guard_msgs in #check (*...* : Std.Rii Nat)
/-- info: 1<...=10 : Std.Roc Nat -/
#guard_msgs in #check 1<...=10
/-- info: 1<...* : Std.Roi Nat -/
#guard_msgs in #check 1<...*
/-- info: 1...10 : Std.Rco Nat -/
#guard_msgs in #check 1...10
/-- info: *...10 : Std.Rio Nat -/
#guard_msgs in #check *...10
/-- info: 1<...10 : Std.Roo Nat -/
#guard_msgs in #check 1<...10

/-!
Synonyms for other ranges.
-/
/-- info: 1...10 : Std.Rco Nat -/
#guard_msgs in #check 1...<10
/-- info: *...10 : Std.Rio Nat -/
#guard_msgs in #check *...<10
/-- info: 1<...10 : Std.Roo Nat -/
#guard_msgs in #check 1<...<10

/-!
Check that responds to both `pp.notation` and `pp.explicit`.
-/
/-- info: { lower := 1, upper := 10 } : Std.Rco Nat -/
#guard_msgs in set_option pp.notation false in #check 1...10
/--
info: @Std.Rco.mk Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
  (@OfNat.ofNat Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) : Std.Rco Nat
-/
#guard_msgs in set_option pp.explicit true in #check 1...10
