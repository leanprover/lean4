namespace foo
  variable A : Type.{1}
  variable a : A
  variable x : A
  variable c : A
end foo

context
  using foo (renaming a->b x->y) (hiding c)
  check b
  check y
  check c -- Error
end

context
  using foo (a x)
  check a
  check x
  check c -- Error
end

context
  using foo (a x) (hiding c) -- Error
end

context
  using foo
  check a
  check c
  check A
end

namespace foo
  variable f : A → A → A
  infix `*`:75 := f
end foo

context
  using foo
  check a * c
end

context
  using [notation] foo -- use only the notation
  check foo.a * foo.c
  check a * c -- Error
end

context
  using [decls] foo -- use only the declarations
  check f a c
  check a*c -- Error
end
