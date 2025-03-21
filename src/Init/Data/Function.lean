/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

prelude
import Init.Core

namespace Function

/--
Transforms a function from pairs into an equivalent two-parameter function.

Examples:
 * `Function.curry (fun (x, y) => x + y) 3 5 = 8`
 * `Function.curry Prod.swap 3 "five" = ("five", 3)`
-/
@[inline]
def curry : (α × β → φ) → α → β → φ := fun f a b => f (a, b)

/--
Transforms a two-parameter function into an equivalent function from pairs.

Examples:
 * `Function.uncurry List.drop (1, ["a", "b", "c"]) = ["b", "c"]`
 * `[("orange", 2), ("android", 3) ].map (Function.uncurry String.take) = ["or", "and"]`
-/
@[inline]
def uncurry : (α → β → φ) → α × β → φ := fun f a => f a.1 a.2

@[simp]
theorem curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
  rfl

@[simp]
theorem uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
  funext fun ⟨_a, _b⟩ => rfl

@[simp]
theorem uncurry_apply_pair {α β γ} (f : α → β → γ) (x : α) (y : β) : uncurry f (x, y) = f x y :=
  rfl

@[simp]
theorem curry_apply {α β γ} (f : α × β → γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

end Function
