

class Foo (α : Type) : Type := (u : Unit := ())
class Bar (α : Type) : Type := (u : Unit := ())
class Top : Type := (u : Unit := ())

instance FooAll (α : Type) : Foo α := {u:=()}
instance BarNat : Bar Nat := {u:=()}

set_option synthInstance.checkSynthOrder false in
instance FooBarToTop (α : Type) [Foo α] [Bar α] : Top := {u:=()}

set_option pp.all true

#synth Top
