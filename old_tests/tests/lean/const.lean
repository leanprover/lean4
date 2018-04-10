--

universe variables u
definition foo {A : Type u} [H : inhabited A] : A :=
inhabited.rec (λa, a) H

constant bla {A : Type u} [H : inhabited A] : Type 1

set_option pp.implicit true

section
  variable A : Type u
  variable S : inhabited A
  variable B : @bla A S
  #check B
  #check @foo A S
end
