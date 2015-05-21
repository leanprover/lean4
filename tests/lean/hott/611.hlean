open is_trunc
attribute trunc.rec [recursor]

definition my_elim {n : trunc_index} {A : Type} {P : Type}
  [Pt : is_trunc n P] (H : A → P) : trunc n A → P :=
begin
  intro x, induction x,
  apply H, assumption
end
