set_option pp.mvars false

/--
error: failed to synthesize
  OfNat (Sort _) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort _
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
axiom bla : 1

/--
error: failed to synthesize
  OfNat (Sort _) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort _
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
structure Foo where
  foo : 1

/--
error: failed to synthesize
  OfNat (Sort _) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort _
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
inductive Bla (x : 1) : Type
