example : ∃ a b c : nat, a = b + c :=
begin
  existsi [_, _, _],
  refl,
  repeat {exact 0}
end
