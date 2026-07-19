module

/-! Applying `[instance]` after the fact should check for appropriate reducibility. -/

/--
warning: Definition `unexposed` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
public def unexposed : Inhabited Nat := inferInstance

/-- warning: instance `unexposed` must be marked with `@[expose]` -/
#guard_msgs in
attribute [instance] unexposed

/--
warning: Definition `unexposed` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
attribute [local instance] unexposed

/--
warning: Definition `exposed` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
@[expose]
public def exposed : Inhabited Nat := inferInstance

/--
warning: Definition `exposed` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
attribute [instance] exposed

/--
warning: Definition `exposed` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this
definition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`.
-/
#guard_msgs in
attribute [local instance] exposed

@[expose, instance_reducible]
public def exposedAndReducible : Inhabited Nat := inferInstance

#guard_msgs in
attribute [instance] exposedAndReducible

#guard_msgs in
attribute [local instance] exposedAndReducible

instance bla : Add Int := ⟨Int.add⟩

#guard_msgs in
attribute [irreducible] bla
