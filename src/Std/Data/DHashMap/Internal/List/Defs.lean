/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.BinderPredicates

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: definitions on lists needed to state the well-formedness predicate
-/

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

namespace Std.DHashMap.Internal.List

def Pairwise (P : α → α → Prop) : List α → Prop
| [] => True
| (x::xs) => (∀ y ∈ xs, P x y) ∧ Pairwise P xs

def keys : List (Σ a, β a) → List α
  | [] => []
  | ⟨k, _⟩ :: l => k :: keys l

/-- The well-formedness predicate for `AssocList` says that keys are pairwise distinct. -/
structure DistinctKeys [BEq α] (l : List (Σ a, β a)) : Prop where
  distinct : Pairwise (fun a b => (a == b) = false) (keys l)

def values {β : Type v} : List ((_ : α) × β) → List β
  | [] => []
  | ⟨_, v⟩ :: l => v :: values l

end Std.DHashMap.Internal.List
