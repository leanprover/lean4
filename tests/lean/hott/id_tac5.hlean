open equiv

constant rec_on_ua {A B : Type} {P : A ≃ B → Type}
  (f : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q)) : P f

set_option pp.universes true
set_option pp.implicit true
set_option pp.notation false

check @rec_on_ua

attribute rec_on_ua [recursor]

print [recursor] rec_on_ua
