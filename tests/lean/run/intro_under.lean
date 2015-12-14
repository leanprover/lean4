example (p q r : Prop) : p → q → r → r :=
begin
  intro _ _ Hr,
  assumption
end
