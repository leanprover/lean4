/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Core

set_option linter.all true

set_option doc.verso true

universe u v

/-!
# Bind-level "may return" predicate

{lit}`MayReturnM x a` is a Prop-level statement that {lit}`a` is classically in the image of {lit}`x`.
-/

/--
{lean}`ErasesToM x y` says the property-tagged {name}`x` is bind-faithful to {name}`y`: binding
{name}`x` and forgetting the property agrees with binding {name}`y`.
-/
@[expose] public def ErasesToM {α : Type u} {m : Type u → Type v} [Bind m] {P : α → Prop}
    (x : m {b : α // P b}) (y : m α) : Prop :=
  ∀ {β} (k : α → m β), x >>= (fun a => k a.val) = y >>= k

/--
{lean}`MayReturnM x a` says {name}`a` cannot be classically excluded from {name}`x`'s image.
In a pure sense, the function {lean}`MayReturnM x : α → Prop` is the strongest postcondition for
{name}`x`.
-/
@[expose] public def MayReturnM {m : Type u → Type v} [Bind m] {α : Type u} (x : m α) (a : α) : Prop :=
  Not (Exists fun y : m {b : α // b ≠ a} => ErasesToM y x)

/--
Whether {name}`m` has an attach function. For each {given}`x`, {lean}`attach x` tags {name}`x`
with a {name}`Subtype` proof for {name}`MayReturnM` and erases back to {name}`x`.
-/
@[expose] public def IsAttach {m : Type u → Type v} [Bind m]
    (attach : ⦃α : Type u⦄ → (x : m α) → m {a : α // MayReturnM x a}) : Prop :=
  ∀ ⦃α⦄ (x : m α), ErasesToM (attach x) x
