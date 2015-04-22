section
  open [notations] [coercions] nat
  check 1 + 2
  check add -- Error aliases were not created
end

section
  open [declarations] [notations] nat
  variable a : nat
  check a + a
  check add a a
  check a + 1 -- Error coercion from num to nat was not loaded
end

section
  open - [classes] nat
  variable a : nat
  check a + a
  check add a a
  check a + 1
  definition foo1 : inhabited nat :=
  _ -- Error inhabited instances was not loaded
end

section
  open - [classes] [decls] nat
  variable a : nat
  check a + a
  check add a a -- Error aliases were not created
  check a + 1
  definition foo2 : inhabited nat :=
  _ -- Error inhabited instances was not loaded
end

section
  open [classes] nat
  definition foo3 : inhabited nat :=
  _

  variable a : nat
  check a + a -- Error notation declarations were not loaded
end
