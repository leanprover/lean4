open is_trunc unit

protected definition trunc.elim {n : trunc_index} {A : Type} {P : Type}
  [Pt : is_trunc n P] (H : A → P) : trunc n A → P :=
trunc.rec H

attribute trunc.rec  [recursor 6]
attribute trunc.elim [recursor 6]

example (x : trunc -1 unit) : unit :=
begin
  induction x, exact star
end
