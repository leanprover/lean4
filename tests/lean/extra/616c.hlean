open eq
definition my_elim {A P : Type} {R : A → A → Type} (Pc : A → P)
  (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (x : type_quotient R) : P :=
begin
  induction x,
    exact (Pc a),
    refine (!tr_constant ⬝ Pp H)
end
