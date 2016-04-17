constants (A : Type) (B : A → Type) (C : Π a, B a → Type)
constants (f : Π a b, C a b → (true → true))
attribute f [coercion]

print coercions

constants (a : A) (b : B a) (c : C a b)

definition messy₁ := f a b c
definition messy₂ := f a b c trivial

eval messy₁
eval messy₂

set_option pp.proofs false

eval messy₁
eval messy₂
