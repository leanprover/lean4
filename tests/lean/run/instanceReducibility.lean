module

/-! Reducibility of instances should default to `[instance_reducible]` but be overridable. -/

instance i1 : Inhabited Nat := inferInstance

/--
info: @[implicit_reducible] private def i1 : Inhabited Nat :=
inferInstance
-/
#guard_msgs in
#print i1

@[reducible] instance i2 : Inhabited Nat := inferInstance

/--
info: @[reducible] private def i2 : Inhabited Nat :=
inferInstance
-/
#guard_msgs in
#print i2

/--
warning: instance `_private.lean.run.instanceReducibility.0.i3` must be marked with `@[reducible]` or `@[implicit_reducible]`
-/
#guard_msgs in
@[irreducible] instance i3 : Inhabited Nat := inferInstance

/--
info: @[irreducible] private def i3 : Inhabited Nat :=
inferInstance
-/
#guard_msgs in
#print i3
