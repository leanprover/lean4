open nat
namespace foo
section
  parameter (X : Type₁)
  definition A {n : ℕ} : Type₁ := X
  definition B : Type₁ := X
  variable {n : ℕ}
  check @A n
  check foo.A nat
  check foo.A (X × B)
  check @foo.A (X × B) 10
  check @foo.A (@foo.B (@A n)) n
  check @foo.A (@foo.B (@foo.A X n)) n
  check @foo.A (@foo.B (@foo.A nat n)) n

  set_option pp.full_names true
  check A
  check foo.A nat
  check @foo.A (X × B) 10
  check @foo.A (@foo.B (@foo.A X n)) n
  check @foo.A (@foo.B (@foo.A nat n)) n

  set_option pp.full_names false

  set_option pp.implicit true
  check @A n
  check @foo.A nat 10
  check @foo.A X n
  set_option pp.full_names true
  check @foo.A X n
  check @A n

  set_option pp.full_names false
  check @foo.A X n
  check @foo.A B n
  check @foo.A (@foo.B (@A n)) n
  check @foo.A (@foo.B (@foo.A X n)) n
  check @foo.A (@foo.B (@foo.A nat n)) n
  check @A n
end
end foo
