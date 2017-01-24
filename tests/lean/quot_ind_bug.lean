open quotient

variables {A : Type} [s : setoid A] {B : quotient s → Prop} (c : ∀ (a : A), B (quotient.mk a)) (a : A)
check (quotient.ind c ⟦a⟧ : B ⟦a⟧)
check c a
eval (quotient.ind c ⟦a⟧ : B ⟦a⟧)
