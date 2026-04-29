/-! Registering an instance whose target type is not a class should warn. -/

structure Foo where
  x : Nat

class Bar where
  x : Nat

/-- error: instance `instFoo` target `Foo` is not a type class. -/
#guard_msgs in
instance instFoo : Foo := ⟨0⟩

-- Applying @[instance] to a non-class def should also warn
def instFoo2 : Foo := ⟨1⟩

/-- error: instance `instFoo2` target `Foo` is not a type class. -/
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

/-- error: instance `instQux` target `Qux Nat` is not a type class. -/
#guard_msgs in
instance instQux : Qux Nat := ⟨0⟩
