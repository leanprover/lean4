-- HoTT
import hit.circle
open circle eq int pi

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
    { apply arrow_pathover_left, intro b, apply concato_eq, apply pathover_eq_r,
      rewrite [power_con,transport_code_loop]},
  end
