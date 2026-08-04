/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Init.Control.Id
public import Init.Data.List.Basic
public import Init.Data.List.Control

/-!
# Effect-free `ForIn` containers

`PureForIn` and `PureForIn'` identify the containers whose loop produces its elements without
effects, so that iterating is iterating over the list `ForIn.toList` computes in `Id`, and
`LawfulMemForInId` identifies those whose `Membership` agrees with that `Id` loop.
-/

@[expose] public section

namespace Std.Internal

universe u u₁ v w
/-- Containers whose `Membership` is exactly the elements the `Id` loop enumerates. The `Iff` says
the loop yields all members and nothing else; it constrains neither their order nor their
multiplicity. -/
class LawfulMemForInId (ρ : Type w) (α : Type u₁) [d : Membership α ρ] [ForIn Id ρ α] :
    Prop where
  /-- The elements of `ForIn.toList xs` are the members of `xs`. -/
  mem_toList_iff {a : α} {xs : ρ} : a ∈ ForIn.toList xs ↔ a ∈ xs

/-- Containers whose `ForIn` loop produces its elements without effects in `m`, so iterating over
`xs` is iterating over the list `ForIn.toList` computes in `Id`. Only the loop body may have
effects. -/
class PureForIn (m : Type u → Type v) (ρ : Type w) (α : Type u₁) [Monad m]
    [ForIn m ρ α] [ForIn Id ρ α] : Prop where
  /-- Iterating over `xs` is iterating over `ForIn.toList xs`. -/
  forIn_eq {β : Type u} (xs : ρ) (init : β) (f : α → β → m (ForInStep β)) :
    forIn xs init f = forIn (ForIn.toList xs) init f

/-- Containers whose `ForIn'` loop produces its elements without effects in `m`, carrying a
membership proof for each. -/
class PureForIn' (m : Type u → Type v) (ρ : Type w) (α : Type u₁) [Monad m]
    {d : Membership α ρ} [ForIn' m ρ α d] [ForIn Id ρ α]
    [LawfulMemForInId ρ α] : Prop where
  /-- Iterating over `xs` is iterating over `ForIn.toList xs`. -/
  forIn'_eq {β : Type u} (xs : ρ) (init : β) (f : (a : α) → a ∈ xs → β → m (ForInStep β)) :
    forIn' xs init f = forIn' (ForIn.toList xs) init fun a h b =>
      f a (LawfulMemForInId.mem_toList_iff.mp h) b


end Std.Internal
