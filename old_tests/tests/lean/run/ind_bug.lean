constant N : Type.{1}
constant I : Type.{1}

namespace foo
  inductive p (a : N) : Prop
  | intro : p
end foo

open foo

namespace bla
  inductive p (a : I) : Prop
  | intro : p
end bla
