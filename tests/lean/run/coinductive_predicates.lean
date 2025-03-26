open Lean.Order

-- set_option trace.Elab.definition.partialFixpoint true
-- set_option trace.Elab.definition.partialFixpoint.induction true

@[partial_fixpoint_monotone] theorem monotone_exists
    {α} [PartialOrder α] {β} (f : α → β → Prop)
    (h : monotone f) :
    monotone (fun x => Exists (f x)) :=
  fun x y hxy ⟨w, hw⟩ => ⟨w, monotone_apply w f h x y hxy hw⟩

@[partial_fixpoint_monotone] theorem monotone_and
    {α} [PartialOrder α] (f₁ : α → Prop) (f₂ : α → Prop)
    (h₁ : monotone f₁) (h₂ : monotone f₂) :
    monotone (fun x => f₁ x ∧ f₂ x) :=
  fun x y hxy ⟨hfx₁, hfx₂⟩ => ⟨h₁ x y hxy hfx₁, h₂ x y hxy hfx₂⟩

def infinite_chain {α} (step : α → Option α) (x : α) : Prop :=
  ∃ y, step x = some y ∧ (infinite_chain step y)
  greatest_fixpoint

#check infinite_chain.fixpoint_induct

def infinite_chain_fixpoint {α} (step : α → Option α) (x : α) :
  infinite_chain step x = ∃ y, step x = some y ∧ infinite_chain step y := by
    rw [infinite_chain]

theorem infinite_chain.coind {α} (P : α → Prop) (step : α → Option α)
  (h : ∀ (x : α), P x → ∃ y, step x = some y ∧ P y) :
  ∀ x, P x → infinite_chain step x := by
    apply infinite_chain.fixpoint_induct
    apply h
