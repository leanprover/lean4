notation `⟪`:max t:(foldr `,` (e r, and.intro e r)) `⟫`:0 := t

check ⟪ trivial, trivial, trivial ⟫

theorem tst (a b c d : Prop) : a ∧ b ∧ c ∧ d ↔ d ∧ c ∧ b ∧ a :=
begin
  apply iff.intro,
  begin
    intro H,
    match H with
    | ⟪ H₁, H₂, H₃, H₄ ⟫ := ⟪ H₄, H₃, H₂, H₁ ⟫
    end
  end,
  begin
    intro H,
    match H with
    | ⟪ H₁, H₂, H₃, H₄ ⟫ :=
      begin
        repeat [apply and.intro | assumption]
      end
    end
  end
end

print definition tst

theorem tst2 (a b c d : Prop) : a ∧ b ∧ c ∧ d ↔ d ∧ c ∧ b ∧ a :=
begin
  apply iff.intro,
  repeat (intro H;  repeat [cases H with [H', H] | apply and.intro | assumption])
end

print definition tst2
