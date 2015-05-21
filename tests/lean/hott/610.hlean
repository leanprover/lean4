import hit.type_quotient
attribute type_quotient.elim [recursor 6]

definition my_elim_on {A : Type} {R : A → A → Type} {P : Type} (x : type_quotient R)
                      (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') : P :=
begin
  induction x,
  exact Pc a,
  exact Pp H
end
