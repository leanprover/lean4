set_option blast.simp  false
set_option blast.subst false

set_option blast.trace true
example (a b c : Prop) : (a ↔ b) → ((a ∧ (c ∨ b)) ↔ (b ∧ (c ∨ a))) :=
by blast

/-
example (a b c : Prop) : (a ↔ b) → ((a ∧ (c ∨ (b ↔ a))) ↔ (b ∧ (c ∨ (a ↔ b)))) :=
by blast

example (a₁ a₂ b₁ b₂ : Prop) : (a₁ ↔ b₁) → (a₂ ↔ b₂) → (a₁ ∧ a₂ ∧ a₁ ∧ a₂ ↔ b₁ ∧ b₂ ∧ b₁ ∧ b₂) :=
by blast

definition lemma1 (a₁ a₂ b₁ b₂ : Prop) : (a₁ = b₁) → (a₂ ↔ b₂) → (a₁ ∧ a₂ ∧ a₁ ∧ a₂ ↔ b₁ ∧ b₂ ∧ b₁ ∧ b₂) :=
by blast

print lemma1
-/
