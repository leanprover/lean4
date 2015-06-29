definition bar := bool
example (b : bar) : bool :=
begin
  rewrite [↓bar],
  assumption
end
