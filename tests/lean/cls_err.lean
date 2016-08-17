--

inductive [class] H (A : Type)
| mk : A → H

definition foo {A : Type} [h : H A] : A :=
H.rec (λa, a) h

section
  variable A : Type
  variable h : H A
  definition tst : A :=
  foo
end
