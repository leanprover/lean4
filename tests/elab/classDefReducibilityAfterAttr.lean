/-!
# Class-typed `def` reducibility warning checks actual status

The `classDefReducibility` warning should check the actual reducibility status
after all attributes have been applied, not just syntactic modifiers.
This ensures attributes that set reducibility during `.afterCompilation`
(like Mathlib's `to_additive (attr := implicit_reducible)`) are respected.
-/

class Foo where
  x : Nat

/-! Warning should fire when no reducibility attribute is present. -/
/--
warning: Definition `baz` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
def baz : Foo := ⟨42⟩

/-! No warning with direct `implicit_reducible`. -/
#guard_msgs in
@[instance_reducible]
def qux : Foo := ⟨42⟩

/-! No warning with `reducible`. -/
#guard_msgs in
@[reducible]
def quux : Foo := ⟨42⟩

/-! No warning with `irreducible`. -/
#guard_msgs in
@[irreducible]
def corge : Foo := ⟨42⟩
