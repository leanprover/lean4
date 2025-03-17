/-!
Johannes Hölzl pointed out that the `partial_fixpoint` machinery can be applied to `Prop` to define
inductive or (when using the dual order) coinductive predicates.

Without an induction principle this isn't so useful, though.
-/

open Lean.Order
set_option trace.Elab.definition.partialFixpoint true
-- set_option trace.Elab.definition.partialFixpoint.induction true
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

/-
The following models a coinductive predicate defined as
```
coinductive infinite_chain step : α → Prop where
| intro : ∀ y x, step x = some y → infinite_chain step y → infinite_chain step
```
-/
def infinite_chain {α} (step : α → Option α) (x : α) : Prop :=
  ∃ y, step x = some y ∧ (infinite_chain step y)
  partial_fixpoint

theorem infinite_chain.intro {α} (step : α → Option α) (y x : α) :
    step x = some y → infinite_chain step y → infinite_chain step x := by
  intros; unfold infinite_chain; simp [*]

theorem infinite_chain.coinduct {α} (P : α → Prop) (step : α → Option α)
  (h : ∀ (x : α), P x → ∃ y, step x = some y ∧ P y) :
  ∀ x, P x → infinite_chain step x := by
  apply infinite_chain.fixpoint_induct step
    (motive := fun i => ∀ (x : α), P x → i x)
  case adm =>
    clear h step
    apply admissible_pi
    intro a
    intro c hchain h hPa Q ⟨f, hcf, hfaQ⟩
    subst Q
    apply h f hcf hPa
  case h =>
    intro ic hPic x hPx
    obtain ⟨y, hstepx, h⟩ := h x hPx
    exact ⟨y, hstepx, hPic y h⟩

/--
Isabelle generates a stronger coinduction theorem from
```
coinductive infinite_chain :: "('a ⇒ 'a option) ⇒ 'a ⇒ bool" for step :: "'a ⇒ 'a option" where
 intro: "infinite_chain step x" if "step x = Some y" and "infinite_chain step y"
```
Note the occurrence of `infinite_chain` in the step:
```
  Scratch.infinite_chain.coinduct:
    ?X ?x ⟹
    (⋀x. ?X x ⟹ ∃xa y. x = xa ∧ ?step xa = Some y ∧ (?X y ∨ infinite_chain ?step y)) ⟹
    infinite_chain ?step ?x
```
We can prove that from the one above.
-/
theorem infinite_chain.coinduct_strong {α} (P : α → Prop) (step : α → Option α)
  (h : ∀ (x : α), P x → ∃ y, step x = some y ∧ (P y ∨ infinite_chain step y)) :
  ∀ x, P x → infinite_chain step x := by
  suffices ∀ x, (P x ∨ infinite_chain step x) → infinite_chain step x by
    intro x hPx
    exact this x (.inl hPx)
  apply infinite_chain.coinduct
  intro x hor
  cases hor
  next hPx => exact h _ hPx
  next hicx =>
    unfold infinite_chain at hicx
    obtain ⟨y, hstepx, h⟩ := hicx
    exact ⟨y, hstepx, .inr h⟩
