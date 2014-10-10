import logic
set_option pp.notation false
constant A    : Type
constants a b : A
constant P    : A → Type
constant H₁   : a = a
constant H₂   : P a
constant H₃   : a = b
constant f {A : Type} (a : A) : a = a
eval eq.rec H₂ (f a)
eval eq.rec H₂ H₁
eval eq.rec H₂ H₃
eval eq.rec H₂ (eq.refl a)
eval λ (A : Type) (a b : A) (H₁ : a = a) (P : A → Prop) (H₂ : P a) (H₃ : a = a) (c : A), eq.rec (eq.rec H₂ H₁) H₃
check @eq.rec A a P H₂ a
check λ H : a = a, H₂
inductive to_type {B : Type} : B → Type :=
mk : Π (b : B), to_type b

definition tst1 : to_type (λ H : a = a, H₂) := to_type.mk (@eq.rec A a P H₂ a)
check to_type.mk(λ H : a = a, H₂)
check to_type.mk(@eq.rec A a P H₂ a)
check to_type.mk(λ H : a = a, H₂) = to_type.mk(@eq.rec A a P H₂ a)
check to_type.mk(eq.rec H₂ H₁) = to_type.mk(H₂)
check to_type.mk(eq.rec H₂ (f a)) = to_type.mk(H₂)
