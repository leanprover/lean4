def Set' (α : Type) := α → Prop

def Mem' {α} (s : Set' α) (a : α) : Prop :=
  s a

instance {α} : Membership α (Set' α) :=
  ⟨Mem'⟩

def Subset' {α} (s₁ s₂ : Set' α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

instance {α} : LE (Set' α) :=
  ⟨Subset'⟩

instance {α} : HasSubset (Set' α) :=
  ⟨(· ≤ ·)⟩

theorem subset_def' {α} {s t : Set' α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

example {α γ} (f : α → Nat → Set' γ) (V : Set' γ) :
    (∃ i, (∃ a r, 0 < r ∧ i = f a r) ∧ id i ⊆ V) ↔
      ∃ a r, 0 < r ∧ f a r ⊆ V := by
  grind only [= subset_def', = id.eq_1, cases Or]
