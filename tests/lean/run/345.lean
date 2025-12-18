set_option pp.mvars false

/--
error: failed to synthesize instance of type class
  OfNat (Sort _) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort _
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
axiom bla : 1

/--
error: failed to synthesize instance of type class
  OfNat (Sort _) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort _
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
structure Foo where
  foo : 1

/--
error: failed to synthesize instance of type class
  OfNat (Sort _) 1
numerals are polymorphic in Lean, but the numeral `1` cannot be used in a context where the expected type is
  Sort _
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
inductive Bla (x : 1) : Type
