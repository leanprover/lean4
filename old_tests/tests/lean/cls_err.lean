--
universe variables u
class inductive H (A : Type u)
| mk : A → H

definition foo {A : Type u} [h : H A] : A :=
H.rec (λa, a) h

section
  variable A : Type u
  variable h : H A
  definition tst : A :=
  foo
end
