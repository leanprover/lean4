instance Pi.hasLe {ι : Type u} {α : ι → Type v} [∀ i, LE (α i)] :
  LE (∀ i, α i) where le x y := ∀ i, x i ≤ y i

variable {ι : Type u} {α : ι → Type v} [inst : (i : ι) → LE (α i)]

set_option trace.Meta.isDefEq.assign true

#check @Pi.hasLe ι _ inst
