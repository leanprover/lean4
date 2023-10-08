/-
Here is an artificial example where temporary metavariables created by typeclass resolution
would otherwise leak into nested typeclass resolution unless we catch it.
-/

class Foo  (α : Type) : Type := (x : Unit)
class Bar  (α : Type) : Type := (x : Unit)
class HasParam (α : Type) [Bar α] : Type := (x : Unit)

instance FooToBar (α : Type) [Foo α] : Bar α := {x:=()}

-- Note: there is an implicit `FooToBar` inside the second argument of the return type.
instance HasParamInst (α : Type) [h : Foo α] : HasParam α := {x:=()}

class Top : Type := (x : Unit)

-- Note: `AllFoo` is a weird, universal instance.
instance AllFoo (α : Type) : Foo α := {x:=()}

/-
When the subgoal `[@HasParam α (@FooToBar α (AllFoo α))]` is triggered, `α` is not known.

This happens for two reasons:

1. The return type `Top` does not include `α`.
2. The universal `AllFoo α` instance obviates the need to take a building-block class as argument.

Thus we would be tempted to call nested typeclass resolution on `Foo <tmp-mvar>`.
-/
instance Bad (α : Type) [HasParam α] : Top := Top.mk ()
def foo [Top] : Unit := ()

set_option pp.all true
set_option trace.class_instances true
set_option trace.type_context.complete_instance true

#check @foo _

/-
[class_instances]  class-instance resolution trace
[class_instances] (0) ?x_0 : Top := @Bad ?x_1 ?x_2
[class_instances] (1) ?x_2 : @HasParam ?x_1 (@FooToBar ?x_1 (AllFoo ?x_1)) := @HasParamInst ?x_3 ?x_4
[type_context.complete_instance] would have synthed: Foo ?x_3
-/
