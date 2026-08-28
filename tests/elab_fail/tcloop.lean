class A (α : Type u) where
  a : Unit

class B (α : Type u) where
  a : Unit

instance [s : B (Array α)] : A α  where
  a := ()

instance [s : A (Array α)] : B α where
  a := ()

set_option warn.classDefReducibility false in
def f : B Nat :=
  inferInstance
