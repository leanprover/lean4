

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

set_option pp.all true

#synth Top
