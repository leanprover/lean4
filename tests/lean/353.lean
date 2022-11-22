class ArrSort (α : Sort u1) where
  Arr : α → α → Sort u2
class Arr (α : Sort u1) (γ : Sort u2) where
  Arr : α → α → γ
infix:70 " ~> " => Arr.Arr
@[default_instance]
instance inst1 {α : Sort _} [ArrSort α] : Arr α (Sort _) := { Arr := ArrSort.Arr }
instance inst2 : ArrSort Prop := { Arr := λ a b => a → b }

set_option pp.all true
set_option trace.Meta.debug true
structure Function' where
  map : ∀ {a₁ a₂ : Bool}, (a₁ ~> a₂) ~> (a₁ ~> a₂)
