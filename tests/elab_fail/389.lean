structure Foo (A : Sort _) := (foo : A)
structure Bar (A : Sort _) extends Foo A := (bar : A)
instance {A} : Coe (Bar A) (Foo A) := {coe := Bar.toFoo}
def getFoo {A} (F : Foo A) := F.foo
def bar : Bar Nat := {foo := 0, bar := 1}

#check getFoo bar
#check (getFoo bar : Nat)
