section
  parameter A : Type
  parameter a : A
  parameter c : A
  omit A
  include A
  include A
  omit A
  parameter B : Type
  parameter b : B
  parameter d : B
  include A
  include a
  include c
  definition foo := b

  inductive tst (C : Type) :=
  mk : tst C
end

check foo
check tst
