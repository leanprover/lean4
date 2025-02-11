/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.Def
import Std.Classes.Ord

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

namespace Std.DTreeMap.Internal.Impl

/-- The size information stored in the tree. -/
@[inline]
def size : Impl α β → Nat
  | inner sz _ _ _ _ => sz
  | leaf => 0

@[Std.Internal.tree_tac] theorem size_leaf : (Impl.leaf : Impl α β).size = 0 := rfl
@[Std.Internal.tree_tac] theorem size_inner {sz k v l r} : (Impl.inner sz k v l r : Impl α β).size = sz := rfl

/-- Returns `true` if the given key is contained in the map. -/
def contains [Ord α] (k : α) (t : Impl α β) : Bool :=
  match t with
  | .leaf => false
  | .inner _ k' _ l r =>
    match compare k k' with
    | .lt => contains k l
    | .gt => contains k r
    | .eq => true

instance [Ord α] : Membership α (Impl α β) where
  mem t a := t.contains a

instance [Ord α] {m : Impl α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

/-- Returns `true` if the tree is empty. -/
@[inline]
def isEmpty (t : Impl α β) : Bool :=
  match t with
  | .leaf => true
  | .inner _ _ _ _ _ => false

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def get? [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) : Option (β k) :=
  match t with
  | .leaf => none
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get? k l
    | .gt => get? k r
    | .eq => some (cast (congrArg β (compare_eq_iff_eq.mp h).symm) v')

/-- Returns the value for the key `k`. -/
def get [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) (hlk : t.contains k = true) : β k :=
  match t with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get k l (by simpa [contains, h] using hlk)
    | .gt => get k r (by simpa [contains, h] using hlk)
    | .eq => cast (congrArg β (compare_eq_iff_eq.mp h).symm) v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) [Inhabited (β k)] : β k :=
  match t with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get! k l
    | .gt => get! k r
    | .eq => cast (congrArg β (compare_eq_iff_eq.mp h).symm) v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) (fallback : β k) : β k :=
  match t with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => getD k l fallback
    | .gt => getD k r fallback
    | .eq => cast (congrArg β (compare_eq_iff_eq.mp h).symm) v'

namespace Const

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def get? [Ord α] (k : α) (t : Impl α (fun _ => δ)) : Option δ :=
  match t with
  | .leaf => none
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => get? k l
    | .gt => get? k r
    | .eq => some v'

/-- Returns the value for the key `k`. -/
def get [Ord α] (k : α) (t : Impl α (fun _ => δ)) (hlk : t.contains k = true) : δ :=
  match t with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get k l (by simpa [contains, h] using hlk)
    | .gt => get k r (by simpa [contains, h] using hlk)
    | .eq => v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] (k : α) (t : Impl α (fun _ => δ)) [Inhabited δ] : δ :=
  match t with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => get! k l
    | .gt => get! k r
    | .eq => v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] (k : α) (t : Impl α (fun _ => δ)) (fallback : δ) : δ :=
  match t with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => getD k l fallback
    | .gt => getD k r fallback
    | .eq => v'

end Const

/-- Folds the given function over the mappings in the tree in ascending order. -/
@[specialize]
def foldlM {m} [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ) : Impl α β → m δ
  | .leaf => pure init
  | .inner _ k v l r => do
    let left ← foldlM f init l
    let middle ← f left k v
    foldlM f middle r

/-- Folds the given function over the mappings in the tree in ascending order. -/
@[specialize]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : Impl α β) : δ :=
  Id.run (t.foldlM f init)

/-- Folds the given function over the mappings in the tree in descending order. -/
@[specialize]
def foldrM {m} [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ) : Impl α β → m δ
  | .leaf => pure init
  | .inner _ k v l r => do
    let right ← foldlM f init r
    let middle ← f right k v
    foldlM f middle l

/-- Folds the given function over the mappings in the tree in descending order. -/
@[inline]
def foldr (f : δ → (a : α) → β a → δ) (init : δ) (t : Impl α β) : δ :=
  Id.run (t.foldrM f init)

/-- Applies the given function to the mappings in the tree in ascending order. -/
@[inline]
def forM {m} [Monad m] (f : (a : α) → β a → m PUnit) (t : Impl α β) : m PUnit :=
  t.foldlM (fun _ k v => f k v) ⟨⟩

/-- Implementation detail. -/
@[specialize]
def forInStep {m} [Monad m] (f : δ → (a : α) → β a → m (ForInStep δ)) (init : δ) :
    Impl α β → m (ForInStep δ)
  | .leaf => pure (.yield init)
  | .inner _ k v l r => do
    match ← forInStep f init l with
    | ForInStep.done d => return (.done d)
    | ForInStep.yield d =>
      match ← f d k v with
      | ForInStep.done d => return (.done d)
      | ForInStep.yield d => forInStep f d r

/-- Support for the `for` construct in `do` blocks. -/
@[inline]
def forIn {m} [Monad m] (f : δ → (a : α) → β a → m (ForInStep δ)) (init : δ) (t : Impl α β) : m δ := do
  match ← forInStep f init t with
  | ForInStep.done d => return d
  | ForInStep.yield d => return d

/-- Returns a `List` of the keys in order. -/
@[inline] def keys (t : Impl α β) : List α :=
  t.foldr (init := []) fun l k _ => k :: l

/-- Returns an `Array` of the keys in order. -/
@[inline] def keysArray (t : Impl α β) : Array α :=
  t.foldl (init := #[]) fun l k _ => l.push k

/-- Returns a `List` of the key/value pairs in order. -/
@[inline] def toList (t : Impl α β) : List ((a : α) × β a) :=
  t.foldr (init := []) fun l k v => ⟨k, v⟩ :: l

/-- Returns an `Array` of the key/value pairs in order. -/
@[inline] def toArray (t : Impl α β) : Array ((a : α) × β a) :=
  t.foldl (init := #[]) fun l k v => l.push ⟨k, v⟩

namespace Const

variable {β : Type v}

/-- Returns a `List` of the key/value pairs in order. -/
@[inline] def toList (t : Impl α (fun _ => β)) : List (α × β) :=
  t.foldr (init := []) fun l k v => (k, v) :: l

/-- Returns a `List` of the key/value pairs in order. -/
@[inline] def toArray (t : Impl α (fun _ => β)) : Array (α × β) :=
  t.foldl (init := #[]) fun l k v => l.push (k, v)

end Const

end Std.DTreeMap.Internal.Impl
