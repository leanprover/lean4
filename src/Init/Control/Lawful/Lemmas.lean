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
theorem map_inj_of_left_inverse [Applicative m] [LawfulApplicative m] {f : α → β}
    (w : ∃ g : β → α, ∀ x, g (f x) = x) {x y : m α}
    (h : f <$> x = f <$> y) : x = y := by
  rcases w with ⟨g, w⟩
  replace h := congrArg (g <$> ·) h
  simpa [w] using h

-- Mapping by an injective function is injective, as long as the domain is nonempty.
theorem map_inj_of_inj [Applicative m] [LawfulApplicative m] [Nonempty α] {f : α → β}
    (w : ∀ x y, f x = f y → x = y) {x y : m α}
    (h : f <$> x = f <$> y) : x = y := by
  apply map_inj_of_left_inverse ?_ h
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
