import data.nat
open algebra

theorem test {A : Type} [s : comm_ring A] (a b c : A) : a + b + c = a + c + b :=
begin
  rewrite *add.comm
end
