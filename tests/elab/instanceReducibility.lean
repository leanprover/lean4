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

#guard_msgs in
@[irreducible] instance i3 : Inhabited Nat := inferInstance

/--
info: @[irreducible] private def i3 : Inhabited Nat :=
inferInstance
-/
#guard_msgs in
#print i3

#guard_msgs in
set_option warn.classDefReducibility false in
@[irreducible] instance i4 : Inhabited Nat := inferInstance

set_option allowUnsafeReducibility true in
/--
warning: Definition `_private.elab.instanceReducibility.0.i5` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
@[semireducible] instance i5 : Inhabited Nat := inferInstance

-- Why does `i5` not get any warning?
