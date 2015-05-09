import data.nat
open algebra

theorem test {A : Type} [s : comm_ring A] (a b c : A) : a + b + c = a + c + b :=
begin
  rewrite [add.assoc, {b + _}add.comm, -add.assoc]
end

reveal test
print definition test
