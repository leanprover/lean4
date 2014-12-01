prelude section
  variable A : Type
  variable a : A
  variable c : A
  omit A
  include A
  include A
  omit A
  variable B : Type
  variable b : B
  variable d : B
  include A
  include a
  include c
  definition foo := b

  inductive tst (C : Type) :=
  mk : tst C
end

check foo
check tst
