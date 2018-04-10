open nat

definition foo : nat := 30

namespace foo
  definition x : nat := 10
  definition y : nat := 20
end foo

export foo

example : x + y = foo := rfl
