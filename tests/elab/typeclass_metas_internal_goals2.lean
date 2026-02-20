
class Foo (α β : Type) : Type := (u : Unit := ())
class Bar (α β : Type) : Type := (u : Unit := ())
class Top : Type := (u : Unit := ())

instance FooNatA (β : Type) : Foo Nat β := {u:=()}
instance BarANat (α : Type) : Bar α Nat := {u:=()}

set_option synthInstance.checkSynthOrder false in
instance FooBarToTop (α β : Type) [Foo α β] [Bar α β] : Top := {u:=()}

set_option pp.all true

/-- info: @FooBarToTop Nat Nat (FooNatA Nat) (BarANat Nat) -/
#guard_msgs in
#synth Top
