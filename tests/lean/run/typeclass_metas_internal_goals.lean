#exit

namespace T1

class Foo (α : Type) : Type := (u : Unit := ())
class Bar (α : Type) : Type := (u : Unit := ())
class Top : Type := (u : Unit := ())

instance FooAll (α : Type) : Foo α := {u:=()}
instance BarNat : Bar Nat := {u:=()}

instance FooBarToTop (α : Type) [Foo α] [Bar α] : Top := {u:=()}

#synth Top

end T1

namespace T2

class Foo (α β : Type) : Type := (u : Unit := ())
class Bar (α β : Type) : Type := (u : Unit := ())
class Top : Type := (u : Unit := ())

instance FooNatA (β : Type) : Foo Nat β := {u:=()}
instance BarANat (α : Type) : Bar α Nat := {u:=()}

instance FooBarToTop (α β : Type) [Foo α β] [Bar α β] : Top := {u:=()}

#synth Top

end T2

namespace T3

class Base (α : Type) := (u:Unit)
class Depends (α : Type) [Base α] := (u:Unit)
class Top := (u:Unit)

instance AllBase {α : Type} : Base α := {u:=()}
instance DependsNotConstrainingImplicit {α : Type} /- [Base α] -/ {_:Base α} : Depends α := {u:=()}

instance BaseAsImplicit₁ {α : Type} {_:Base α} [Depends α] : Top := {u:=()}
instance BaseAsInstImplicit {α : Type} [Base α] [Depends α] : Top := {u:=()}
instance BaseAsImplicit₂ {α : Type} {_:Base α} [Depends α] : Top := {u:=()}

axiom K : Type
instance BaseK : Base K := {u:=()}

#synth Top

end T3

namespace T4

class Foo (α β γ : Type) := (u:Unit)
class Bar (α β γ : Type) := (u:Unit)
class Top := (u:Unit)
instance FooBarToTop (α β γ : Type) [Foo α β γ] [Bar α β γ] : Top := {u:=()}

instance Foo₁ (β γ : Type) : Foo Unit β γ := {u:=()}
instance Foo₂ (α γ : Type) : Foo α Unit γ := {u:=()}
instance Foo₃ (α β : Type) : Foo α β Unit := {u:=()}

instance Foo₁₂ (γ : Type) : Foo Unit Nat γ := {u:=()}
instance Foo₂₃ (α : Type) : Foo α Unit Nat := {u:=()}
instance Foo₃₁ (β : Type) : Foo Nat β Unit := {u:=()}

instance Bar0 : Bar Unit Int (List Int) := {u:=()}

#synth Top

end T4
