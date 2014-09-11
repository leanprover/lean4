import data.nat

section foo
  parameter A : Type
  definition id (a : A) := a
  variable a : nat
  check _root_.id nat a
end foo

namespace n1
section foo
  parameter A : Type
  definition id (a : A) := a
  variable a : nat
  check n1.id _ a
end foo
end n1
