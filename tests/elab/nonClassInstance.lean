/-! Registering an instance whose target type is not a class should warn. -/

structure Foo where
  x : Nat

class Bar where
  x : Nat

/--
error: The declaration `instFoo` should not be an instance as its return type `Foo` is not a type class.
-/
#guard_msgs in
instance instFoo : Foo := ⟨0⟩

-- Applying @[instance] to a non-class def should also warn
def instFoo2 : Foo := ⟨1⟩

/--
error: The declaration `instFoo2` should not be an instance as its return type `Foo` is not a type class.
-/
#guard_msgs in
attribute [instance] instFoo2

-- No warning for a proper class instance
#guard_msgs in
instance : Bar := ⟨0⟩

-- No warning for a class instance with parameters
class Baz (α : Type) where
  x : α

#guard_msgs in
instance : Baz Nat := ⟨0⟩

-- Warning for non-class with parameters
structure Qux (α : Type) where
  x : α

/--
error: The declaration `instQux` should not be an instance as its return type `Qux Nat` is not a type class.
-/
#guard_msgs in
instance instQux : Qux Nat := ⟨0⟩

/-- warning: declaration uses `sorry` -/
#guard_msgs in
instance bad : ∀ n : Nat, sorry := by sorry
