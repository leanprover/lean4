import logic

namespace setoid
  structure setoid : Type :=
  (carrier : Type) (eqv : carrier → carrier → Prop)

  infix `≈` := setoid.eqv _

  attribute setoid.carrier [coercion]

  inductive morphism (s1 s2 : setoid) : Type :=
  mk : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism s1 s2

  set_option pp.universes true

  check morphism.mk
  check λ (s1 s2 : setoid), s1
  check λ (s1 s2 : Type), s1

  inductive morphism2 (s1 : setoid) (s2 : setoid) : Type :=
  mk : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism2 s1 s2

  check morphism2.mk
end setoid
