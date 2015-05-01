open eq

definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) : (p ⬝ q⁻¹) ⬝ q = p :=
begin
  generalize p,
  eapply (eq.rec_on q),
  intro p,
  apply (eq.rec_on p),
  apply idp
end
