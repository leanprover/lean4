/-
Here is an example where temporary metavariables from typeclass resolution
could spill into nested typeclass resolution, for which the outer TC succeeds
iff:

1. the inner TC is still called, even with the leaked tmp mvars
2. the inner TC is allowed to assign the leaked tmp mvars

This example will *NOT* work in Lean4.

Although it would be easy to allow inner TC to set the outer TC tmp mvars,
the issue is that the solution to the inner TC problem may not be unique,
and it would be extremely difficult to allow backtracking from the outer TC
through to the inner TC.

In Lean4, inner TC can be called with leaked temporary mvars from the outer TC,
but they are treated as opaque, just as regular mvars are treated in the outer TC.
So, this example will fail.
-/

class Foo  (α : Type) : Type := (x : Unit)
class Zoo  (α : Type) : Type := (x : Unit)
class Bar  (α : Type) : Type := (x : Unit)
class HasParam (α : Type) [Bar α] : Type := (x : Unit)

instance FooToBar (α : Type) [f : Foo α] : Bar α :=
match f.x with
| () => {x:=()}

instance ZooToBar (α : Type) [z : Zoo α] : Bar α :=
match z.x with
| () => {x:=()}

instance HasParamInst (α : Type) [h : Foo α] : HasParam α := {x:=()}

class Top : Type := (x : Unit)

instance FooInt : Foo Int := {x:=()}
instance AllZoo (α : Type) : Zoo α := {x:=()}

instance Bad (α : Type) [HasParam α] : Top := Top.mk ()

set_option pp.all true
set_option trace.class_instances true
set_option trace.type_context.complete_instance true

def foo [Top] : Unit := ()
#check @foo _

/-
[class_instances]  class-instance resolution trace
[class_instances] (0) ?x_0 : Top := @Bad ?x_1 ?x_2
[class_instances] (1) ?x_2 : @HasParam ?x_1 (@ZooToBar ?x_1 (AllZoo ?x_1)) := @HasParamInst ?x_3 ?x_4
[type_context.complete_instance] would have synthed: Foo ?x_3
[type_context.complete_instance] would have synthed: Foo ?x_3
failed is_def_eq
-/

def couldWork : Top :=
@Bad Int (@HasParamInst Int FooInt)

#print couldWork
/-
def couldWork : Top :=
@Bad Int (@HasParamInst Int FooInt)
-/
