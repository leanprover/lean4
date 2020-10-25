
class Foo (α β : Type) : Type := (u : Unit := ())
class Bar (α β : Type) : Type := (u : Unit := ())
class Top : Type := (u : Unit := ())

instance FooNatA (β : Type) : Foo Nat β := {u:=()}
instance BarANat (α : Type) : Bar α Nat := {u:=()}

instance FooBarToTop (α β : Type) [Foo α β] [Bar α β] : Top := {u:=()}

set_option pp.all true

#synth Top
