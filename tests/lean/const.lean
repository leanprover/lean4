import logic


definition foo {A : Type} [H : inhabited A] : A :=
inhabited.rec (λa, a) H

constant bla {A : Type} [H : inhabited A] : Type.{1}

set_option pp.implicit true

section
  variable A : Type
  variable S : inhabited A
  variable B : @bla A _
  check B
  check @foo A _
end
