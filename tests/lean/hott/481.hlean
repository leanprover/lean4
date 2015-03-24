open equiv eq is_equiv is_trunc

definition foo {A B : Type} (f : A ≃ B) (f' : A → B)
               (H' : is_equiv f') (p : to_fun f = f') : p = p :=
begin
  cases p,
  esimp
end
