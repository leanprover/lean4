open eq tactic
open eq (rec_on)

definition concat_whisker2 {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) ⬝ (whiskerL p' b) = (whiskerL p b) ⬝ (whiskerR a q') :=
begin
  apply (rec_on b),
  apply (rec_on a),
  apply ((concat_1p _)⁻¹),
end
