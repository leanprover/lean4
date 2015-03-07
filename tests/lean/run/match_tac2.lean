example (a b c : Prop) : a ∧ b ↔ b ∧ a :=
begin
  apply iff.intro,
  {intro H,
   match H with
   |  and.intro H₁ H₂ := by apply and.intro; assumption
   end},
  {intro H,
   match H with
   | and.intro H₁ H₂ := by apply and.intro; assumption
   end},
end
