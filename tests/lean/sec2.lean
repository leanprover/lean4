structure A : Type := mk
structure B : Type := mk
constant f : A → B
constant g : B → B
constant a : A

namespace foo
  attribute f [coercion]
  print coercions
  check g a
end foo

check g a -- Error

section boo
  attribute f [coercion]
  print coercions
  check g a
end boo
-- The metaobjects defined in the section persist to the outer level.
-- This is not a bug. The idea is: we can use the scope to define
-- auxiliary variables that are then used to define classes/instances/etc.
-- That is, the whole point of the scope is to define these metaobjects.
check g a -- Ok
