/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
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
