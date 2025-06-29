import Std.Internal.Rat
open Std.Internal

/-!
Tests for `pp.numericTypes` and `pp.natLit`

RFC #3021
-/

open Lean

section

/-!
Both raw nat lits and non-raw natural numbers pretty print the same by default
-/
/-- info: 22 : Nat -/
#guard_msgs in #check nat_lit 22
/-- info: 22 : Nat -/
#guard_msgs in #check 22

set_option pp.natLit true

/-!
The raw nat lit pretty prints with the `nat_lit` prefix when `pp.natLit` is true.
-/
/-- info: nat_lit 22 : Nat -/
#guard_msgs in #check nat_lit 22
/-- info: 22 : Nat -/
#guard_msgs in #check 22

end

section
set_option pp.numericTypes true

/-!
The `pp.numericTypes` option sets `pp.natLit` to true.
-/
/-- info: nat_lit 22 : Nat -/
#guard_msgs in #check nat_lit 22

/-!
Natural number literal
-/
/-- info: (22 : Rat) : Rat -/
#guard_msgs in #check (22 : Rat)

/-!
Negative integer literal
-/
/-- info: (-22 : Rat) : Rat -/
#guard_msgs in #check (-22 : Rat)

/-!
Rational literal of two natural numbers
-/
/-- info: (22 / 17 : Rat) : Rat -/
#guard_msgs in #check (22 / 17 : Rat)

/-!
Rational literal of a negative integer and a rational
-/
/-- info: (-22 / 17 : Rat) : Rat -/
#guard_msgs in #check (-22 / 17 : Rat)

/-!
Not a rational literal since the denominator is negative.
-/
/-- info: (-22 : Rat) / (-17 : Rat) : Rat -/
#guard_msgs in #check (-22 / -17 : Rat)

/-!
Natural number literal for `Fin`.
-/
/-- info: (17 : Fin (22 : Nat)) : Fin (22 : Nat) -/
#guard_msgs in #check (17 : Fin 22)

/-!
Natural number literal for `Nat`.
-/
/-- info: (2 : Nat) : Nat -/
#guard_msgs in #check 2

/-!
Natural number literals in the context of an equation.
-/
/-- info: (2 : Nat) + (1 : Nat) = (3 : Nat) : Prop -/
#guard_msgs in #check 2 + 1 = 3

/-!
Testing `pp.explicit` override. The `2` appears as `nat_lit` in the `OfNat.ofNat` expression.
-/
set_option pp.explicit true in
/-- info: @OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)) : Nat -/
#guard_msgs in #check 2

end

section
set_option pp.all true

/-!
Testing `pp.all`.
-/
/-- info: @OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)) : Nat -/
#guard_msgs in #check 2

/-!
Testing that `pp.all` overrides `pp.natLit`.
-/
set_option pp.natLit false
/-- info: @OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)) : Nat -/
#guard_msgs in #check 2

end
