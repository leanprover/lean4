/-
The current plan is to allow typeclass resolution to be triggered when there are still
expression metavariables in the goal.

It will return:

success: it succeeded without needing to unify a regular metavar with anything
fail: it failed without even getting a chance to unify a regular metavar with anything
wait: it would have needed to unify a regular metavar with something

If it returns `wait`, the elaborator may try again later after learning more about the goal.

Note: this only applies to expression metavariables.
See typeclasses_with_umetavariables.lean for a discussion of universe metavariables.
-/

class Foo (b : Bool)
class Bar (b : Bool)
class Rig (b : Bool)

@[instance] axiom FooTrue : Foo true
@[instance] axiom FooToBar (b : Bool) : HasCoe (Foo b) (Bar b)

/- [success] In the following example, `Foo.mk _ : Foo ?m₁` would coerce to `Bar ?m₁`,
since resolution would succeed without ever needing to unify `?m₁`. -/
noncomputable def tcSuccess :=
[Bar.mk _, Foo.mk _, Bar.mk true]

/- [failure] In this example, since there is no coercion from `Foo` to `Rig`,
resolution would fail immediately without bothering to wait.-/
noncomputable def tcFail :=
[Rig.mk _, Foo.mk _]


@[instance] axiom FooToRig : HasCoe (Foo true) (Rig true)

/- [wait] In this example, the coercion from `Foo.mk _ : Foo ?m₁` to `Rig ?m₁`
would wait, but then be queried again later and succeed.-/
noncomputable def tcWait :=
[Rig.mk _, Foo.mk _, Rig.mk true]
