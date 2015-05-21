-- HoTT
import hit.circle
open circle eq int

attribute circle.rec circle.elim [recursor 4]

protected definition my_code (x : circle) : Type₀ :=
begin
  induction x,
  { exact ℤ},
  { apply ua, apply equiv_succ}
end

protected definition my_decode {x : circle} : my_code x → base = x :=
begin
  induction x,
  { exact power loop},
  { apply eq_of_homotopy, intro a,
    refine !arrow.arrow_transport ⬝ !transport_eq_r ⬝ _,
    rewrite [transport_code_loop_inv,power_con,succ_pred]}
end
