import logic

inductive sigma {A : Type} (B : A → Type) :=
mk : Π (a : A), B a → sigma B

#projections sigma :: proj1 proj2

check sigma.proj1
check sigma.proj2

variables {A : Type} {B : A → Type}
variables (a : A) (b : B a)

theorem tst1 : sigma.proj1 (sigma.mk a b) = a :=
rfl

theorem tst2 : sigma.proj2 (sigma.mk a b) = b :=
rfl
