/-
Here is an example where typeclass resolution triggers nested typeclass resolution.
-/

class Ring   (α : Type) : Type := (x : Unit)
class Double (α : Type) : Type := (x : Unit)
class Foo    (α : Type) [Double α] : Type := (x : Unit)

instance RingToDouble (α : Type) [Ring α] : Double α := Double.mk α ()

-- Note: The return type is really `@Foo α (@RingToDouble α s)`.
instance RingFoo (α : Type) [s : Ring α] : Foo α := Foo.mk α ()

instance RingInt : Ring Int := Ring.mk Int ()
instance DoubleInt : Double Int := Double.mk Int ()

def foo [@Foo Int DoubleInt] : Unit := ()

set_option pp.all true
set_option trace.class_instances true
set_option trace.type_context.complete_instance true

#check @foo _

/-
[class_instances]  class-instance resolution trace
[class_instances] (0) ?x_0 : @Foo Int DoubleInt := @RingFoo ?x_1 ?x_2
[type_context.complete_instance] about to synth: Ring Int
[class_instances]  class-instance resolution trace
[class_instances] (0) ?x_3 : Ring Int := RingInt
[class_instances] (1) ?x_2 : Ring Int := RingInt
@foo (@RingFoo Int RingInt) : Unit
-/
