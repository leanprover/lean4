
/--
error: failed to synthesize
  OfNat (Sort ?u.1) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort ?u.1
due to the absence of the instance above
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
axiom bla : 1

/--
error: failed to synthesize
  OfNat (Sort ?u.8) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort ?u.8
due to the absence of the instance above
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
structure Foo where
  foo : 1

/--
error: failed to synthesize
  OfNat (Sort ?u.210) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort ?u.210
due to the absence of the instance above
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
inductive Bla (x : 1) : Type
