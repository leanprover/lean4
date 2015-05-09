open quot

variables {A : Type} [s : setoid A] {B : quot s → Prop} (c : ∀ (a : A), B (quot.mk a)) (a : A)
check quot.ind c ⟦a⟧
check c a
eval quot.ind c ⟦a⟧
