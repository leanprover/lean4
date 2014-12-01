import logic.eq

inductive sigma2 {A : Type} (B : A → Type) :=
mk : Π (a : A), B a → sigma2 B

#projections sigma2 :: proj1 proj2

check sigma2.proj1
check sigma2.proj2

variables {A : Type} {B : A → Type}
variables (a : A) (b : B a)

theorem tst1 : sigma2.proj1 (sigma2.mk a b) = a :=
rfl

theorem tst2 : sigma2.proj2 (sigma2.mk a b) = b :=
rfl
