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

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

open List (Pairwise)

namespace Std.DHashMap.Internal.List

/-- Internal implementation detail of the hash map -/
def keys : List ((a : α) × β a) → List α
  | [] => []
  | ⟨k, _⟩ :: l => k :: keys l

/-- Internal implementation detail of the hash map -/
structure DistinctKeys [BEq α] (l : List ((a : α) × β a)) : Prop where
  /-- Internal implementation detail of the hash map -/
  distinct : Pairwise (fun a b => (a == b) = false) (keys l)

/-- Internal implementation detail of the hash map -/
def values {β : Type v} : List ((_ : α) × β) → List β
  | [] => []
  | ⟨_, v⟩ :: l => v :: values l

end Std.DHashMap.Internal.List
