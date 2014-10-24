import hott.path tools.tactic
open path

definition concat_pV_p {A : Type} {x y z : A} (p : x ≈ z) (q : y ≈ z) : (p ⬝ q⁻¹) ⬝ q ≈ p :=
begin
  generalize p,
  apply (path.induction_on q),
  intro p,
  apply (path.induction_on p),
  apply idp
end
