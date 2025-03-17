/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Control.Lawful.Basic
import Init.RCases
import Init.ByCases

-- Mapping by a function with a left inverse is injective.
theorem map_inj_of_left_inverse [Functor m] [LawfulFunctor m] {f : α → β}
    (w : ∃ g : β → α, ∀ x, g (f x) = x) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  constructor
  · intro h
    rcases w with ⟨g, w⟩
    replace h := congrArg (g <$> ·) h
    simpa [w] using h
  · rintro rfl
    rfl

-- Mapping by an injective function is injective, as long as the domain is nonempty.
@[simp] theorem map_inj_right_of_nonempty [Functor m] [LawfulFunctor m] [Nonempty α] {f : α → β}
    (w : ∀ {x y}, f x = f y → x = y) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  constructor
  · intro h
    apply (map_inj_of_left_inverse ?_).mp h
    let ⟨a⟩ := ‹Nonempty α›
    refine ⟨?_, ?_⟩
    · intro b
      by_cases p : ∃ a, f a = b
      · exact Exists.choose p
      · exact a
    · intro b
      simp only [exists_apply_eq_apply, ↓reduceDIte]
      apply w
      apply Exists.choose_spec (p := fun a => f a = f b)
  · rintro rfl
    rfl

@[simp] theorem map_inj_right [Monad m] [LawfulMonad m]
    {f : α → β} (h : ∀ {x y : α}, f x = f y → x = y) {x y : m α} :
    f <$> x = f <$> y ↔ x = y := by
  by_cases hempty : Nonempty α
  · exact map_inj_right_of_nonempty h
  · constructor
    · intro h'
      have (z : m α) : z = (do let a ← z; let b ← pure (f a); x) := by
        conv => lhs; rw [← bind_pure z]
        congr; funext a
        exact (hempty ⟨a⟩).elim
      rw [this x, this y]
      rw [← bind_assoc, ← map_eq_pure_bind, h', map_eq_pure_bind, bind_assoc]
    · intro h'
      rw [h']
