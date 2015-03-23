constants {A B : Type} {P : B → Type} {f : A → B}
(rec_on : Π(b : B) (H : Πa, P (f a)) (H2 : Πa, H a = H a), P b)

example (b : B) (H : Πa, P (f a)) : P b :=
begin
  fapply (rec_on b),
    {exact H},
    {clear b, apply sorry}
end
