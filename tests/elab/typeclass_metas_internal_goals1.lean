

class Foo (α : Type) : Type where (u : Unit := ())
class Bar (α : Type) : Type where (u : Unit := ())
class Top : Type where (u : Unit := ())

instance FooAll (α : Type) : Foo α := {u:=()}
instance BarNat : Bar Nat := {u:=()}

set_option synthInstance.checkSynthOrder false in
instance FooBarToTop (α : Type) [Foo α] [Bar α] : Top := {u:=()}

set_option pp.all true

/-- info: @FooBarToTop Nat (FooAll Nat) BarNat -/
#guard_msgs in
#synth Top
