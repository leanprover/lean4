-- HoTT
open is_equiv equiv eq

definition my_rec_on_ua [recursor] {A B : Type} {P : A ≃ B → Type}
  (f : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q)) : P f :=
right_inv equiv_of_eq f ▸ H (ua f)

theorem foo {A B : Type} (f : A ≃ B) : A = B :=
begin
  induction f using my_rec_on_ua,
  assumption
end
