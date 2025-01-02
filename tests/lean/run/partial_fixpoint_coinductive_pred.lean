/-!
Johannes Hölzl pointed out that the `partial_fixpoint` machinery can be applied to `Prop` to define
inductive or (when using the dual order) coinductive predicates.

Without an induction principle this isn't so useful, though.
-/

open Lean.Order

instance : PartialOrder Prop where
  rel x y := y → x -- NB: Dual
  rel_refl := fun x => x
  rel_trans h₁ h₂ := fun x => h₁ (h₂ x)
  rel_antisymm h₁ h₂ := propext ⟨h₂, h₁⟩

instance : CCPO Prop where
  csup c := ∀ p, c p → p
  csup_spec := fun _ =>
    ⟨fun h y hcy hx => h hx y hcy, fun h hx y hcy => h y hcy hx ⟩

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

def univ (n : Nat) : Prop :=
  univ (n + 1)
partial_fixpoint

def infinite_chain {α} (step : α → Option α) (x : α) : Prop :=
  ∃ y, step x = some y ∧ infinite_chain step y
partial_fixpoint

theorem infinite_chain.intro {α} (step : α → Option α) (y x : α) :
    step x = some y → infinite_chain step y → infinite_chain step x := by
  intros; unfold infinite_chain; simp [*]

-- For a (co)-induction principle we'd need an induction from `partial_fixpoint`
