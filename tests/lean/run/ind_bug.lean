import logic
variable N : Type.{1}
variable I : Type.{1}

namespace foo
  inductive p (a : N) : Prop :=
  intro : p a
end foo

open foo

namespace bla
  inductive p (a : I) : Prop :=
  intro : p a
end bla
