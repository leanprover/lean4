import logic

inductive H [class] (A : Type) :=
mk : A → H A

definition foo {A : Type} [h : H A] : A :=
H.rec (λa, a) h

section
  variable A : Type
  variable h : H A
  definition tst : A :=
  foo
end
