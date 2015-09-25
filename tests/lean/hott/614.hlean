import homotopy.circle

open circle eq int pi

attribute circle.rec [recursor]

protected definition my_decode {x : circle} (c : circle.code x) : base = x :=
begin
  induction x,
  { revert c, exact power loop },
  { apply arrow_pathover_left, intro b, apply concato_eq, apply pathover_eq_r,
    rewrite [power_con,transport_code_loop]},
end

protected definition my_decode' {x : circle} : circle.code x → base = x :=
begin
  induction x,
  { exact power loop},
  { apply arrow_pathover_left, intro b, apply concato_eq, apply pathover_eq_r,
    rewrite [power_con,transport_code_loop]},
end
