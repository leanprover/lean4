import data.nat
open nat algebra

theorem tst (x : nat) (H1 : x = 0) : x = 0 :=
begin
  rewrite *add_zero,
  rewrite H1
end
