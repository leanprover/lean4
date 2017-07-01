example (n) : nat.pred n = n :=
begin
  dsimp {fail_if_unchaged := ff}
end
