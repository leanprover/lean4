open eq tactic
open eq (rec_on)

definition concat_whisker2 {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whisker_right a q) ⬝ (whisker_left p' b) = (whisker_left p b) ⬝ (whisker_right a q') :=
begin
  apply (rec_on b),
  apply (rec_on a),
  apply ((idp_con _)⁻¹),
end
