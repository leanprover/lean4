import algebra.ring
open algebra

definition foo {A : Type} [s : monoid A] (a : A) :=
a * a

example {A : Type} [s : comm_ring A] (a b : A) (H : foo a = a) : a * a = a :=
begin
  rewrite [↓foo a, H]
end
