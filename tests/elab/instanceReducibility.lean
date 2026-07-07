module

/-! Reducibility of instances should default to `[instance_reducible]` but be overridable. -/

instance i1 : Inhabited Nat := inferInstance

/--
info: @[instance_reducible] private def i1 : Inhabited Nat :=
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
warning: instance `_private.elab.instanceReducibility.0.i3` must be marked with `@[reducible]`, `@[instance_reducible]` or `@[implicit_reducible]`
-/
#guard_msgs in
@[semireducible] instance i3 : Inhabited Nat := inferInstance

/--
info: @[irreducible] private def i3 : Inhabited Nat :=
inferInstance
-/
#guard_msgs in
#print i3

#guard_msgs in
set_option warn.classDefReducibility false in
@[irreducible] instance i4 : Inhabited Nat := inferInstance
