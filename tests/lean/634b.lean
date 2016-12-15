open nat
namespace foo
section
  parameter (X : Type)
  definition A {n : ℕ} : Type := X
  definition B : Type := X
  variable {n : ℕ}
  check @A n
  check foo.A
  check foo.A
  check @foo.A 10
  check @foo.A n
  check @foo.A n
  check @foo.A  n

  set_option pp.full_names true
  check A
  check foo.A
  check @foo.A 10
  check @foo.A n
  check @foo.A n

  set_option pp.full_names false

  set_option pp.implicit true
  check @A n
  check @foo.A 10
  check @foo.A n
  set_option pp.full_names true
  check @foo.A n
  check @A n

  set_option pp.full_names false
  check @foo.A n
  check @foo.A n
  check @foo.A n
  check @foo.A n
  check @foo.A n
  check @A n
end
end foo
