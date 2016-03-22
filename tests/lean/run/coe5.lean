import logic

namespace setoid
  structure setoid : Type :=
  (carrier : Type) (eqv : carrier → carrier → Prop)

  infix `≈` := setoid.eqv _

  attribute setoid.carrier [coercion]

  inductive morphism (s1 s2 : setoid) : Type :=
  mk : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism s1 s2

  check morphism.mk
  check λ (s1 s2 : setoid), s1
  check λ (s1 s2 : Type), s1

  inductive morphism2 (s1 : setoid) (s2 : setoid) : Type :=
  mk : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism2 s1 s2

  check morphism2
  check morphism2.mk

  structure my_struct : Type :=
  (s1 s2 : setoid) (s3 s4 : setoid) (f₁ : morphism2 s1 s2) (f₂ : morphism2 s3 s4)

  check my_struct
  definition tst2 : Type.{3} := my_struct.{1 2 1 2}
end setoid
