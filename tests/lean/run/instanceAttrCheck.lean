/-!
# Check that the `instance` attribute is on an instance
-/

inductive Foo where | mk

/--
error: type class instance expected
  Foo
-/
#guard_msgs in
instance : Foo := ⟨⟩

/--
error: type class instance expected
  Foo
-/
#guard_msgs in
@[instance] def fn : Foo := ⟨⟩
