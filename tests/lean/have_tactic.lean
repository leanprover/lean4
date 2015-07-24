example (a b c : nat) : a = b → b = c → a = c :=
begin
  intro h₁ h₂,
  have a = c, from eq.trans h₁ _,
end
