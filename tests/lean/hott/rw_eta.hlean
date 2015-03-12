open eq is_equiv funext

constant f : nat → nat → nat

example : (λ x y : nat, f x y) = f :=
rfl

namespace hide

variables {A : Type} {B : A → Type} {C : Πa, B a → Type}

definition homotopy2 [reducible] (f g : Πa b, C a b) : Type :=
Πa b, f a b = g a b
notation f `∼2`:50 g := homotopy2 f g

definition eq_of_homotopy2 {f g : Πa b, C a b} (H : f ∼2 g) : f = g :=
eq_of_homotopy (λa, eq_of_homotopy (H a))

definition apD100 {f g : Πa b, C a b} (p : f = g) : f ∼2 g :=
λa b, apD10 (apD10 p a) b


local attribute eq_of_homotopy [reducible]

definition foo (f g : Πa b, C a b) (H : f ∼2 g) (a : A)
  : apD100 (eq_of_homotopy2 H) a = H a :=
begin
  esimp {apD100, eq_of_homotopy2, eq_of_homotopy},
  rewrite (retr apD10 (λ(a : A), eq_of_homotopy (H a))),
  apply (retr apD10)
end

end hide
