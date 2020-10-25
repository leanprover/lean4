
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

set_option pp.all true

#synth Top
