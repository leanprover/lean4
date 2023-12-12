/-
In contrast to expression metavariables (see: typeclasses_with_emetavariables.lean),
typeclass resolution is not stalled due to the presence of universe metavariables.

In the current C++ implementation, some (but not all) universe metavariables appearing
in typeclass goals are converted to temporary metavariables.
-/

class Foo.{u, v} (α : Type.{u}) : Type.{v}
class Bar.{u} (α : Type) : Type.{u}

@[instance] axiom foo5 : Foo.{0, 5} Unit

def synthFoo {X : Type} [inst : Foo X] : Foo X := inst

set_option trace.class_instances true
set_option pp.all true

/-
Currently, universe variables in the level params of the *outer-most head symbol*
of the class are converted to temporary metavariables.-/
noncomputable def f1 : Foo Unit := synthFoo

def synthFooBar.{u, v} {X : Type*} [inst : Foo.{u, v} (Bar.{u} X)] : Foo.{u, v} (Bar.{u} X) := inst
@[instance] axiom fooBar5.{u} : Foo.{5, u} (Bar.{5} Unit)

/-
This *nested* universe parameter is not converted into a temporary metavariable, and so this fails.-/
noncomputable def f2 : Foo (Bar Unit) := synthFooBar

/-
Here is the trace:
<<
[class_instances] (0) ?x_0 : Foo.{?u_0 ?u_1} (Bar.{?l__fresh.4.77} Unit) := fooBar5.{?u_2}
failed is_def_eq
[class_instances] (0) ?x_0 : Foo.{?u_0 ?u_1} (Bar.{?l__fresh.4.77} Unit) := foo5
failed is_def_eq
>>

Note that the universe metavariable in question is converted to a temporary metavariable in only one of the two occurrences.
-/
