import hit.circle

open circle eq int

attribute circle.rec [recursor]

protected definition my_decode {x : circle} (c : circle.code x) : base = x :=
begin
  induction x,
  { revert c, exact power loop },
  { apply eq_of_homotopy, intro a,
    refine !arrow.arrow_transport ⬝ !transport_eq_r ⬝ _,
    rewrite [transport_code_loop_inv,power_con,succ_pred]
  }
end

protected definition my_decode' {x : circle} : circle.code x → base = x :=
begin
  induction x,
  { exact power loop},
  { apply eq_of_homotopy, intro a,
    refine !arrow.arrow_transport ⬝ !transport_eq_r ⬝ _,
    rewrite [transport_code_loop_inv,power_con,succ_pred]
  }
end
