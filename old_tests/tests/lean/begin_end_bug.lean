example (a b c : nat) : a = b → a = c → b = c :=
assume hab hac,
have b = a, begin trace a, symmetry, assumption end,
begin
  transitivity,
  exact this,
  exact hac
end
