import logic

namespace setoid
  structure setoid : Type :=
  (carrier : Type) (eqv : carrier → carrier → Prop)

  infix `≈` := setoid.eqv _

  attribute setoid.carrier [coercion]

  inductive morphism (s1 s2 : setoid) : Type :=
  mk_morphism : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism s1 s2

end setoid
