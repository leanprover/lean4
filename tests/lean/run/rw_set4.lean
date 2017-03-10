open tactic

attribute [congr, priority std.priority.default+1]
theorem forall_congr_prop_eq {P₁ P₂ Q₁ Q₂ : Prop} :
  P₁ = P₂ → (P₂ → Q₁ = Q₂) → (P₁ → Q₁) = (P₂ → Q₂) :=
sorry

#print [congr] default

example (A : Type) (a b c : A) : (a = b) → (a = c) → a = b := by simp {contextual := tt}
example (A : Type) (a b c : A) : (a = c) → (a = b) → a = b := by simp {contextual := tt}
