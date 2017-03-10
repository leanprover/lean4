open quotient

variables {A : Type} [s : setoid A] {B : quotient s → Prop} (c : ∀ (a : A), B (quotient.mk a)) (a : A)
#check (quotient.ind c ⟦a⟧ : B ⟦a⟧)
#check c a
#reduce (quotient.ind c ⟦a⟧ : B ⟦a⟧)
