/-!
# Check types when pretty printing dot notation for structure projections

In type mismatch errors, the 'object of dot notation' might not be valid for dot notation.
-/

structure Foo : Type where
  out : Nat

/-!
Was printing `true.out`, but it should have been `Foo.out true`.
-/
/--
error: application type mismatch
  Foo.out true
argument
  true
has type
  Bool : Type
but is expected to have type
  Foo : Type
---
info: sorry.out : Nat
-/
#guard_msgs in #check Foo.out true

/-!
Verifying that generalized field notation does not have this bug.
-/
def Foo.out' (f : Foo) : Nat := f.out
/--
error: application type mismatch
  Foo.out' true
argument
  true
has type
  Bool : Type
but is expected to have type
  Foo : Type
---
info: sorry.out' : Nat
-/
#guard_msgs in #check Foo.out' true

/-!
Verifying that projection notation still pretty prints as normal.
-/
section
variable (f : Foo)
/-- info: f.out : Nat -/
#guard_msgs in #check f.out
end

/-!
Verifying that projection notation still pretty prints through type synonys.
-/
section
def Baz := Foo
variable (f : Baz)
/-- info: f.out : Nat -/
#guard_msgs in #check f.out
end
