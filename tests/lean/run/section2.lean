import data.nat

section foo
  variable A : Type
  variable a : nat
end foo

namespace n1
section foo
  variable A : Type
  definition id (a : A) := a
  variable a : nat
  check n1.id _ a
end foo
end n1
