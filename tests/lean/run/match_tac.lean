import data.nat

example (a b c : Prop) : a ∧ b ↔ b ∧ a :=
begin
  apply iff.intro,
  {intro H,
   match H with
   |  and.intro H₁ H₂ := and.intro H₂ H₁
   end},
  {intro H,
   match H with
   | and.intro H₁ H₂ := and.intro H₂ H₁
   end},
end

open nat

example : ∀ (a b : nat), a = b → b = a
| a a rfl := rfl
