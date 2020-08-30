new_frontend

theorem ex1 (x : Nat) (y : { v // v > x }) (z : Nat) : Nat :=
begin
  clear y x;
  exact z
end

theorem ex2 (x : Nat) (y : { v // v > x }) (z : Nat) : Nat :=
begin
  clear x y;
  exact z
end
