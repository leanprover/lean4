module

/-! Applying `[instance]` after the fact should check for appropriate reducibility. -/

public def unexposed : Inhabited Nat := inferInstance

/-- warning: instance `unexposed` must be marked with `@[expose]` -/
#guard_msgs in
attribute [instance] unexposed

/-- warning: instance `unexposed` must be marked with `@[reducible]` or `@[implicit_reducible]` -/
#guard_msgs in
attribute [local instance] unexposed

@[expose]
public def exposed : Inhabited Nat := inferInstance

/-- warning: instance `exposed` must be marked with `@[reducible]` or `@[implicit_reducible]` -/
#guard_msgs in
attribute [instance] exposed

/-- warning: instance `exposed` must be marked with `@[reducible]` or `@[implicit_reducible]` -/
#guard_msgs in
attribute [local instance] exposed

@[expose, implicit_reducible]
public def exposedAndReducible : Inhabited Nat := inferInstance

#guard_msgs in
attribute [instance] exposedAndReducible

#guard_msgs in
attribute [local instance] exposedAndReducible

instance bla : Add Int := ⟨Int.add⟩

#guard_msgs in
attribute [irreducible] bla
