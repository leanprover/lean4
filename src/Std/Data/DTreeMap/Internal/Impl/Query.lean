/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.Classes.LawfulEqOrd
import Orderedtree.DTreeMap.Internal.Impl.Attr
import Orderedtree.DTreeMap.Internal.Impl.Def
import Orderedtree.Classes.TransOrd
import Lean.Elab.Tactic

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}

namespace Std.DTreeMap.Internal

namespace Impl

/-- The size information stored in the tree. -/
@[inline]
def size : Impl α β → Nat
  | inner sz _ _ _ _ => sz
  | leaf => 0

@[tree_tac] theorem size_leaf : (Impl.leaf : Impl α β).size = 0 := rfl
@[tree_tac] theorem size_inner {sz k v l r} : (Impl.inner sz k v l r : Impl α β).size = sz := rfl

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
    | .eq => some (cast (congrArg β (eq_of_compare h).symm) v')

/-- Returns the value for the key `k`. -/
def get [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) (hlk : t.contains k = true) : β k :=
  match t with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get k l (by simpa [contains, h] using hlk)
    | .gt => get k r (by simpa [contains, h] using hlk)
    | .eq => cast (congrArg β (eq_of_compare h).symm) v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) [Inhabited (β k)] : β k :=
  match t with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get! k l
    | .gt => get! k r
    | .eq => cast (congrArg β (eq_of_compare h).symm) v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] [LawfulEqOrd α] (k : α) (t : Impl α β) (fallback : β k) : β k :=
  match t with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => getD k l fallback
    | .gt => getD k r fallback
    | .eq => cast (congrArg β (eq_of_compare h).symm) v'

namespace Const

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def Const.get? [Ord α] (k : α) (t : Impl α (fun _ => δ)) : Option δ :=
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

/-- The smallest element of `t` that is not less than `k`. Also known as `lookupGE` or `ceil`. -/
@[inline]
def lookupGE [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go (some ⟨ky, y⟩) l
    | .eq => some ⟨ky, y⟩
    | .gt => go best r

/-- The smallest element of `t` that is greater than `k`. Also known as `lookupGT` or `higher`. -/
@[inline]
def lookupGT [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go (some ⟨ky, y⟩) l
    | _ => go best r

/-- The largest element of `t` that is not greater than `k`. Also known as `floor`. -/
@[inline]
def lookupLE [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .lt => go best l
    | .eq => some ⟨ky, y⟩
    | .gt => go (some ⟨ky, y⟩) r

/-- The largest element of `t` that is less than `k`. Also known as `lower`. -/
@[inline]
def lookupLT [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
  | .leaf => best
  | .inner _ ky y l r => match compare k ky with
    | .gt => go (some ⟨ky, y⟩) r
    | _ => go best l

/-- The smallest element of `t`. -/
def min? [Ord α] : Impl α β → Option ((a : α) × β a)
  | .leaf => none
  | .inner _ k v .leaf _ => some ⟨k, v⟩
  | .inner _ _ _ l@(.inner _ _ _ _ _) _ => l.min?

/-- The largest element of `t`. -/
def max? [Ord α] : Impl α β → Option ((a : α) × β a)
  | .leaf => none
  | .inner _ k v _ .leaf => some ⟨k, v⟩
  | .inner _ _ _ _ r@(.inner _ _ _ _ _) => r.max?

/-- Returns the mapping with the `n`-th smallest key, or `none` if `n` is at least `t.size`. -/
def atIndex? [Ord α] : Impl α β → Nat → Option ((a : α) × β a)
  | .leaf, _ => none
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => l.atIndex? n
    | .eq => some ⟨k, v⟩
    | .gt => r.atIndex? (n - l.size - 1)

/-- Returns the mapping with the `n`-th smallest key, or panics if `n` is at least `t.size`. -/
def atIndex! [Ord α] [Inhabited ((a : α) × β a)] : Impl α β → Nat → (a : α) × β a
  | .leaf, _ => panic! "Out-of-bounds access"
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => l.atIndex! n
    | .eq => ⟨k, v⟩
    | .gt => r.atIndex! (n - l.size - 1)

/-- Returns the mapping with the `n`-th smallest key, or `fallback` if `n` is at least `t.size`. -/
def atIndexD [Ord α] : Impl α β → Nat → (a : α) × β a → (a : α) × β a
  | .leaf, _, fallback => fallback
  | .inner _ k v l r, n, fallback =>
    match compare n l.size with
    | .lt => l.atIndexD n fallback
    | .eq => ⟨k, v⟩
    | .gt => r.atIndexD (n - l.size - 1) fallback

/-- Returns the number of mappings whose key is strictly less than `k`. -/
@[inline]
def indexOf [Ord α] (k : α) : Impl α β → Nat :=
  go 0
where
  go (sofar : Nat) : Impl α β → Nat
  | .leaf => sofar
  | .inner _ ky _ l r =>
    match compare k ky with
    | .lt => go sofar l
    | .eq => sofar
    | .gt => go (l.size + 1 + sofar) r
