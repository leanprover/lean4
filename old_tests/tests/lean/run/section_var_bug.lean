section
variable {A : Type}
variable [s : setoid A]
variable {B : quotient s → Type}
include s

attribute [reducible]
protected definition ex (f : Π a, B ⟦a⟧) (a : A) : Σ q, B q :=
sigma.mk ⟦a⟧ (f a)

end
