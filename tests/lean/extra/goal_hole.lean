example (a b c : nat) : a = b → b = c → a = c :=
begin
  intro h₁ h₂,
  exact eq.trans _ h₂
end
