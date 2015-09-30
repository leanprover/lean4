prelude namespace foo
  constant A : Type.{1}
  constant a : A
  constant x : A
  constant c : A
end foo

section
  open foo (renaming a->b x->y) (hiding c)
  check b
  check y
  check c -- Error
end

section
  open foo (a x)
  check a
  check x
  check c -- Error
end

section
  open foo (a x) (hiding c) -- Error
end

section
  open foo
  check a
  check c
  check A
end

namespace foo
  constant f : A → A → A
  infix ` * `:75 := f
end foo

section
  open foo
  check a * c
end

section
  open [notations] foo -- use only the notation
  check foo.a * foo.c
  check a * c -- Error
end

section
  open [decls] foo -- use only the declarations
  check f a c
  check a*c -- Error
end
