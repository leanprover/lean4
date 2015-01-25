import logic

namespace setoid
  inductive setoid : Type :=
  mk_setoid: Π (A : Type), (A → A → Prop) → setoid

  definition carrier (s : setoid)
  := setoid.rec (λ a eq, a) s

  definition eqv {s : setoid} : carrier s → carrier s → Prop
  := setoid.rec (λ a eqv, eqv) s

  infix `≈` := eqv

  attribute carrier [coercion]

  inductive morphism (s1 s2 : setoid) : Type :=
  mk_morphism : Π (f : s1 → s2), (∀ x y, x ≈ y → f x ≈ f y) → morphism s1 s2

end setoid
