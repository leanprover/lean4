context
  open [notations] [coercions] nat
  check 1 + 2
  check add -- Error aliases were not created
end

context
  open [declarations] [notations] nat
  variable a : nat
  check a + a
  check add a a
  check a + 1 -- Error coercion from num to nat was not loaded
end

context
  open - [classes] nat
  variable a : nat
  check a + a
  check add a a
  check a + 1
  definition foo1 : inhabited nat :=
  _ -- Error inhabited instances was not loaded
end

context
  open - [classes] [decls] nat
  variable a : nat
  check a + a
  check add a a -- Error aliases were not created
  check a + 1
  definition foo2 : inhabited nat :=
  _ -- Error inhabited instances was not loaded
end

context
  open [classes] nat
  definition foo3 : inhabited nat :=
  _

  variable a : nat
  check a + a -- Error notation declarations were not loaded
end
