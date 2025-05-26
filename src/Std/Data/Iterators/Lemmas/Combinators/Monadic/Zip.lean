/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Monadic.Zip
import Std.Data.Iterators.Lemmas.Consumers.Monadic

namespace Std.Iterators

variable {α₁ α₂ β₁ β₂ : Type w} {m : Type w → Type w'}

def IterM.Intermediate.zip [Iterator α₁ m β₁] (it₁ : IterM (α := α₁) m β₁)
    (memo : (Option { out : β₁ //
        ∃ it : IterM (α := α₁) m β₁, it.IsPlausibleOutput out }))
    (it₂ : IterM (α := α₂) m β₂) :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) :=
  ⟨⟨it₁, memo, it₂⟩⟩

theorem IterM.zip_eq_intermediateZip [Iterator α₁ m β₁]
    (it₁ : IterM (α := α₁) m β₁) (it₂ : IterM (α := α₂) m β₂) :
    it₁.zip it₂ = Intermediate.zip it₁ none it₂ := rfl

theorem IterM.step_intermediateZip [Monad m] [Iterator α₁ m β₁] [Iterator α₂ m β₂]
    {it₁ : IterM (α := α₁) m β₁}
    {memo : Option { out : β₁ //
        ∃ it : IterM (α := α₁) m β₁, it.IsPlausibleOutput out }}
    {it₂ : IterM (α := α₂) m β₂} :
    (Intermediate.zip it₁ memo it₂).step = (do
      match memo with
      | none =>
        match ← it₁.step with
        | .yield it₁' out hp =>
          pure <| .skip (Intermediate.zip it₁' (some ⟨out, _, _, hp⟩) it₂)
            (.yieldLeft rfl hp)
        | .skip it₁' hp =>
          pure <| .skip (Intermediate.zip it₁' none it₂)
            (.skipLeft rfl hp)
        | .done hp =>
          pure <| .done (.doneLeft rfl hp)
      | some out₁ =>
        match ← it₂.step with
        | .yield it₂' out₂ hp =>
          pure <| .yield (Intermediate.zip it₁ none it₂') (out₁, out₂)
            (.yieldRight rfl hp)
        | .skip it₂' hp =>
          pure <| .skip (Intermediate.zip it₁ (some out₁) it₂')
            (.skipRight rfl hp)
        | .done hp =>
          pure <| .done (.doneRight rfl hp)) := by
  simp only [Intermediate.zip, step, Iterator.step, internalState_toIterM]
  split
  · apply bind_congr
    intro step
    obtain ⟨step, h⟩ := step
    cases step <;> rfl
  · rename_i heq
    cases heq
    apply bind_congr
    intro step
    obtain ⟨step, h⟩ := step
    cases step <;> rfl

end Std.Iterators
