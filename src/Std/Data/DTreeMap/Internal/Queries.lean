/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Nat.Compare
import Std.Data.DTreeMap.Internal.Def
import Std.Data.DTreeMap.Internal.Balanced
import Std.Data.DTreeMap.Internal.Ordered
import Std.Classes.Ord

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w} {m : Type w → Type w}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace Std.DTreeMap.Internal.Impl

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

theorem Ordered.mem_inner_iff_mem_right [Ord α] (sz a v) (l r : Impl α β)
    (k : α) (h : compare k a = .gt) :
    k ∈ inner sz a v l r ↔ k ∈ r := by
  simp only [Membership.mem, contains]
  split <;> simp_all

theorem Ordered.mem_inner_iff_mem_left [Ord α] (sz a v) (l r : Impl α β)
    (k : α) (h : compare k a = .lt) :
    k ∈ inner sz a v l r ↔ k ∈ l := by
  simp only [Membership.mem, contains]
  split <;> simp_all

/-- Returns `true` if the tree is empty. -/
@[inline]
def isEmpty (t : Impl α β) : Bool :=
  match t with
  | .leaf => true
  | .inner _ _ _ _ _ => false

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def get? [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) : Option (β k) :=
  match t with
  | .leaf => none
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get? l k
    | .gt => get? r k
    | .eq => some (cast (congrArg β (compare_eq_iff_eq.mp h).symm) v')

/-- Returns the value for the key `k`. -/
def get [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) (hlk : t.contains k = true) : β k :=
  match t with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get l k (by simpa [contains, h] using hlk)
    | .gt => get r k (by simpa [contains, h] using hlk)
    | .eq => cast (congrArg β (compare_eq_iff_eq.mp h).symm) v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) [Inhabited (β k)] : β k :=
  match t with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get! l k
    | .gt => get! r k
    | .eq => cast (congrArg β (compare_eq_iff_eq.mp h).symm) v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) (fallback : β k) : β k :=
  match t with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => getD l k fallback
    | .gt => getD r k fallback
    | .eq => cast (congrArg β (compare_eq_iff_eq.mp h).symm) v'

/-- Implementation detail of the tree map -/
def getKey? [Ord α] (t : Impl α β) (k : α) : Option α :=
  match t with
  | .leaf => none
  | .inner _ k' _ l r =>
    match compare k k' with
    | .lt => getKey? l k
    | .gt => getKey? r k
    | .eq => some k'

/-- Implementation detail of the tree map -/
def getKey [Ord α] (t : Impl α β) (k : α) (hlk : t.contains k = true) : α :=
  match t with
  | .inner _ k' _ l r =>
    match h : compare k k' with
    | .lt => getKey l k (by simpa [contains, h] using hlk)
    | .gt => getKey r k (by simpa [contains, h] using hlk)
    | .eq => k'

/-- Implementation detail of the tree map -/
def getKey! [Ord α] (t : Impl α β) (k : α) [Inhabited α] : α :=
  match t with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' _ l r =>
    match compare k k' with
    | .lt => getKey! l k
    | .gt => getKey! r k
    | .eq => k'

/-- Implementation detail of the tree map -/
def getKeyD [Ord α] (t : Impl α β) (k : α) (fallback : α) : α :=
  match t with
  | .leaf => fallback
  | .inner _ k' _ l r =>
    match compare k k' with
    | .lt => getKeyD l k fallback
    | .gt => getKeyD r k fallback
    | .eq => k'

namespace Const

/-- Returns the value for the key `k`, or `none` if such a key does not exist. -/
def get? [Ord α] (t : Impl α δ) (k : α) : Option δ :=
  match t with
  | .leaf => none
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => get? l k
    | .gt => get? r k
    | .eq => some v'

/-- Returns the value for the key `k`. -/
def get [Ord α] (t : Impl α δ) (k : α) (hlk : t.contains k = true) : δ :=
  match t with
  | .inner _ k' v' l r =>
    match h : compare k k' with
    | .lt => get l k (by simpa [contains, h] using hlk)
    | .gt => get r k (by simpa [contains, h] using hlk)
    | .eq => v'

/-- Returns the value for the key `k`, or panics if such a key does not exist. -/
def get! [Ord α] (t : Impl α δ) (k : α) [Inhabited δ] : δ :=
  match t with
  | .leaf => panic! "Key is not present in map"
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => get! l k
    | .gt => get! r k
    | .eq => v'

/-- Returns the value for the key `k`, or `fallback` if such a key does not exist. -/
def getD [Ord α] (t : Impl α δ) (k : α) (fallback : δ) : δ :=
  match t with
  | .leaf => fallback
  | .inner _ k' v' l r =>
    match compare k k' with
    | .lt => getD l k fallback
    | .gt => getD r k fallback
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
def foldrM {m} [Monad m] (f : (a : α) → β a → δ → m δ) (init : δ) : Impl α β → m δ
  | .leaf => pure init
  | .inner _ k v l r => do
    let right ← foldrM f init r
    let middle ← f k v right
    foldrM f middle l

/-- Folds the given function over the mappings in the tree in descending order. -/
@[inline]
def foldr (f : (a : α) → β a → δ → δ) (init : δ) (t : Impl α β) : δ :=
  Id.run (t.foldrM f init)

/-- Applies the given function to the mappings in the tree in ascending order. -/
@[inline]
def forM {m} [Monad m] (f : (a : α) → β a → m PUnit) (t : Impl α β) : m PUnit :=
  t.foldlM (fun _ k v => f k v) ⟨⟩

/-- Implementation detail. -/
@[specialize]
def forInStep {m} [Monad m] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) :
    Impl α β → m (ForInStep δ)
  | .leaf => pure (.yield init)
  | .inner _ k v l r => do
    match ← forInStep f init l with
    | ForInStep.done d => return (.done d)
    | ForInStep.yield d =>
      match ← f k v d with
      | ForInStep.done d => return (.done d)
      | ForInStep.yield d => forInStep f d r

/-- Support for the `for` construct in `do` blocks. -/
@[inline]
def forIn {m} [Monad m] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : Impl α β) : m δ := do
  match ← forInStep f init t with
  | ForInStep.done d => return d
  | ForInStep.yield d => return d

/-- Returns a `List` of the keys in order. -/
@[inline] def keys (t : Impl α β) : List α :=
  t.foldr (init := []) fun k _ l => k :: l

/-- Returns an `Array` of the keys in order. -/
@[inline] def keysArray (t : Impl α β) : Array α :=
  t.foldl (init := #[]) fun l k _ => l.push k

/-- Returns a `List` of the values in order. -/
@[inline] def values {β : Type v} (t : Impl α β) : List β :=
  t.foldr (init := []) fun _ v l => v :: l

/-- Returns an `Array` of the values in order. -/
@[inline] def valuesArray {β : Type v} (t : Impl α β) : Array β :=
  t.foldl (init := #[]) fun l _ v => l.push v

/-- Returns a `List` of the key/value pairs in order. -/
@[inline] def toList (t : Impl α β) : List ((a : α) × β a) :=
  t.foldr (init := []) fun k v l => ⟨k, v⟩ :: l

/-- Returns an `Array` of the key/value pairs in order. -/
@[inline] def toArray (t : Impl α β) : Array ((a : α) × β a) :=
  t.foldl (init := #[]) fun l k v => l.push ⟨k, v⟩

namespace Const

variable {β : Type v}

/-- Returns a `List` of the key/value pairs in order. -/
@[inline] def toList (t : Impl α β) : List (α × β) :=
  t.foldr (init := []) fun k v l => (k, v) :: l

/-- Returns a `List` of the key/value pairs in order. -/
@[inline] def toArray (t : Impl α β) : Array (α × β) :=
  t.foldl (init := #[]) fun l k v => l.push (k, v)

end Const

/-- Implementation detail of the tree map -/
def min? [Ord α] : Impl α β → Option ((a : α) × β a)
  | .leaf => none
  | .inner _ k v .leaf _ => some ⟨k, v⟩
  | .inner _ _ _ l _ => l.min?

/-- Implementation detail of the tree map -/
def min [Ord α] : (t : Impl α β) → (h : t.isEmpty = false) → (a : α) × β a
  | .inner _ k v .leaf _, _ => ⟨k, v⟩
  | .inner _ _ _ l@(.inner _ _ _ _ _) _, h => l.min (by simp_all [isEmpty])

/-- Implementation detail of the tree map -/
def min! [Ord α] [Inhabited ((a : α) × β a)] : Impl α β → (a : α) × β a
  | .leaf => panic! "Map is empty"
  | .inner _ k v .leaf _ => ⟨k, v⟩
  | .inner _ _ _ l _ => l.min!

/-- Implementation detail of the tree map -/
def minD [Ord α] : Impl α β → (a : α) × β a → (a : α) × β a
  | .leaf, fallback => fallback
  | .inner _ k v .leaf _, _ => ⟨k, v⟩
  | .inner _ _ _ l _, fallback => l.minD fallback

/-- Implementation detail of the tree map -/
def max? [Ord α] : Impl α β → Option ((a : α) × β a)
  | .leaf => none
  | .inner _ k v _ .leaf => some ⟨k, v⟩
  | .inner _ _ _ _ r => r.max?

/-- Implementation detail of the tree map -/
def max [Ord α] : (t : Impl α β) → (h : t.isEmpty = false) → (a : α) × β a
  | .inner _ k v .leaf _, _ => ⟨k, v⟩
  | .inner _ _ _ l@(.inner _ _ _ _ _) _, h => l.max (by simp_all [isEmpty])

/-- Implementation detail of the tree map -/
def max! [Ord α] [Inhabited ((a : α) × β a)] : Impl α β → (a : α) × β a
  | .leaf => panic! "Map is empty"
  | .inner _ k v _ .leaf => ⟨k, v⟩
  | .inner _ _ _ _ r => r.max!

/-- Implementation detail of the tree map -/
def maxD [Ord α] : Impl α β → (a : α) × β a → (a : α) × β a
  | .leaf, fallback => fallback
  | .inner _ k v _ .leaf, _ => ⟨k, v⟩
  | .inner _ _ _ _ r, fallback => r.maxD fallback

/-- Implementation detail of the tree map -/
def minKey? [Ord α] : Impl α β → Option α
  | .leaf => none
  | .inner _ k _ .leaf _ => some k
  | .inner _ _ _ l _ => l.minKey?

/-- Implementation detail of the tree map -/
def minKey [Ord α] : (t : Impl α β) → (h : t.isEmpty = false) → α
  | .inner _ k _ .leaf _, _ => k
  | .inner _ _ _ l@(.inner _ _ _ _ _) _, h => l.minKey (by simp_all [isEmpty])

/-- The smallest key of `t`. Returns the given fallback value if the map is empty. -/
def minKey! [Ord α] [Inhabited α] : Impl α β → α
  | .leaf => panic! "Map is empty"
  | .inner _ k _ .leaf _ => k
  | .inner _ _ _ l _ => l.minKey!

/-- Implementation detail of the tree map -/
def minKeyD [Ord α] : Impl α β → α → α
  | .leaf, fallback => fallback
  | .inner _ k _ .leaf _, _ => k
  | .inner _ _ _ l _, fallback => l.minKeyD fallback

/-- Implementation detail of the tree map -/
def maxKey? [Ord α] : Impl α β → Option α
  | .leaf => none
  | .inner _ k _ _ .leaf => some k
  | .inner _ _ _ _ r => r.maxKey?

/-- Implementation detail of the tree map -/
def maxKey [Ord α] : (t : Impl α β) → (h : t.isEmpty = false) → α
  | .inner _ k _ .leaf _, _ => k
  | .inner _ _ _ l@(.inner _ _ _ _ _) _, h => l.maxKey (by simp_all [isEmpty])

/-- Implementation detail of the tree map -/
def maxKey! [Ord α] [Inhabited α] : Impl α β → α
  | .leaf => panic! "Map is empty"
  | .inner _ k _ _ .leaf => k
  | .inner _ _ _ _ r => r.maxKey!

/-- Implementation detail of the tree map -/
def maxKeyD [Ord α] : Impl α β → α → α
  | .leaf, fallback => fallback
  | .inner _ k _ _ .leaf, _ => k
  | .inner _ _ _ _ r, fallback => r.maxKeyD fallback

attribute [Std.Internal.tree_tac] Nat.compare_eq_gt Nat.compare_eq_lt Nat.compare_eq_eq

/-- Implementation detail of the tree map -/
def entryAtIdx [Ord α] : (t : Impl α β) → (hl : t.Balanced) → (n : Nat) → (h : n < t.size) → (a : α) × β a
  | .inner _ k v l' r', hl, n, h =>
    match h : compare n l'.size with
    | .lt => l'.entryAtIdx hl.left n (by simpa only [Std.Internal.tree_tac] using h)
    | .eq => ⟨k, v⟩
    | .gt => r'.entryAtIdx hl.right (n - l'.size - 1) (by simp_all only [Std.Internal.tree_tac]; omega)

/-- Implementation detail of the tree map -/
def entryAtIdx? [Ord α] : Impl α β → Nat → Option ((a : α) × β a)
  | .leaf, _ => none
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => l.entryAtIdx? n
    | .eq => some ⟨k, v⟩
    | .gt => r.entryAtIdx? (n - l.size - 1)

/-- Implementation detail of the tree map -/
def entryAtIdx! [Ord α] [Inhabited ((a : α) × β a)] : Impl α β → Nat → (a : α) × β a
  | .leaf, _ => panic! "Out-of-bounds access"
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => l.entryAtIdx! n
    | .eq => ⟨k, v⟩
    | .gt => r.entryAtIdx! (n - l.size - 1)

/-- Implementation detail of the tree map -/
def entryAtIdxD [Ord α] : Impl α β → Nat → (a : α) × β a → (a : α) × β a
  | .leaf, _, fallback => fallback
  | .inner _ k v l r, n, fallback =>
    match compare n l.size with
    | .lt => l.entryAtIdxD n fallback
    | .eq => ⟨k, v⟩
    | .gt => r.entryAtIdxD (n - l.size - 1) fallback

/-- Implementation detail of the tree map -/
def keyAtIndex [Ord α] : (t : Impl α β) → (hl : t.Balanced) → (n : Nat) → (h : n < t.size) → α
  | .inner _ k _ l' r', hl, n, h =>
    match h : compare n l'.size with
    | .lt => keyAtIndex l' hl.left n (by simpa only [Std.Internal.tree_tac] using h)
    | .eq => k
    | .gt =>
      keyAtIndex r' hl.right (n - l'.size - 1) (by simp_all only [Std.Internal.tree_tac]; omega)

/-- Implementation detail of the tree map -/
def keyAtIndex? [Ord α] : Impl α β → Nat → Option α
  | .leaf, _ => none
  | .inner _ k _ l r, n =>
    match compare n l.size with
    | .lt => keyAtIndex? l n
    | .eq => some k
    | .gt => keyAtIndex? r (n - l.size - 1)

/-- Implementation detail of the tree map -/
def keyAtIndex! [Ord α] [Inhabited α] : Impl α β → Nat → α
  | .leaf, _ => panic! "Out-of-bounds access"
  | .inner _ k _ l r, n =>
    match compare n l.size with
    | .lt => keyAtIndex! l n
    | .eq => k
    | .gt => keyAtIndex! r (n - l.size - 1)

/-- Implementation detail of the tree map -/
def keyAtIndexD [Ord α] : Impl α β → Nat → α → α
  | .leaf, _, fallback => fallback
  | .inner _ k _ l r, n, fallback =>
    match compare n l.size with
    | .lt => keyAtIndexD l n fallback
    | .eq => k
    | .gt => keyAtIndexD r (n - l.size - 1) fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGE? [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .lt => go (some ⟨ky, y⟩) l
      | .eq => some ⟨ky, y⟩
      | .gt => go best r

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGT? [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .lt => go (some ⟨ky, y⟩) l
      | _ => go best r

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLE? [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .lt => go best l
      | .eq => some ⟨ky, y⟩
      | .gt => go (some ⟨ky, y⟩) r

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLT? [Ord α] (k : α) : Impl α β → Option ((a : α) × β a) :=
  go none
where
  go (best : Option ((a : α) × β a)) : Impl α β → Option ((a : α) × β a)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .gt => go (some ⟨ky, y⟩) r
      | _ => go best l

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGE! [Ord α] [Inhabited ((a : α) × β a)] (k : α) (t : Impl α β) : (a : α) × β a :=
  t.getEntryGE? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGT! [Ord α] [Inhabited ((a : α) × β a)] (k : α) (t : Impl α β) : (a : α) × β a :=
  t.getEntryGT? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLE! [Ord α] [Inhabited ((a : α) × β a)] (k : α) (t : Impl α β) : (a : α) × β a :=
  t.getEntryLE? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLT! [Ord α] [Inhabited ((a : α) × β a)] (k : α) (t : Impl α β) : (a : α) × β a :=
  t.getEntryLT? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGED [Ord α] (k : α) (t : Impl α β) (fallback : (a : α) × β a) : (a : α) × β a :=
  t.getEntryGE? k |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGTD [Ord α] (k : α) (t : Impl α β) (fallback : (a : α) × β a) : (a : α) × β a :=
  t.getEntryGT? k |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLED [Ord α] (k : α) (t : Impl α β) (fallback : (a : α) × β a) : (a : α) × β a :=
  t.getEntryLE? k |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLTD [Ord α] (k : α) (t : Impl α β) (fallback : (a : α) × β a) : (a : α) × β a :=
  t.getEntryLT? k |>.getD fallback

/-- Implementation detail of the tree map -/
def getEntryGE [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, (compare a k).isGE) → (a : α) × β a
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => match hkky : compare k ky with
    | .lt => getEntryGED k l ⟨ky, y⟩
    | .eq => ⟨ky, y⟩
    | .gt => getEntryGE k r ho.right <| by
      obtain ⟨a, hm, hc⟩ := he
      refine ⟨a, ?_, hc⟩
      apply Ordered.mem_inner_iff_mem_right .. |>.mp hm
      exact TransCmp.gt_of_isGE_of_gt hc hkky

/-- Implementation detail of the tree map -/
def getEntryGT [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, compare a k = .gt) → (a : α) × β a
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => if hkky : compare k ky = .lt then
        getEntryGTD k l ⟨ky, y⟩
      else
        getEntryGT k r ho.right <| by
          obtain ⟨a, hm, hc⟩ := he
          refine ⟨a, ?_, hc⟩
          apply Ordered.mem_inner_iff_mem_right .. |>.mp hm
          apply TransCmp.gt_of_gt_of_isGE hc
          simpa [← Ordering.isGE_eq_false, Bool.not_eq_false] using hkky

/-- Implementation detail of the tree map -/
def getEntryLE [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, (compare a k).isLE) → (a : α) × β a
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => match hkky : compare k ky with
    | .gt => getEntryLED k r ⟨ky, y⟩
    | .eq => ⟨ky, y⟩
    | .lt => getEntryLE k l ho.left <| by
      obtain ⟨a, hm, hc⟩ := he
      refine ⟨a, ?_, hc⟩
      apply Ordered.mem_inner_iff_mem_left .. |>.mp hm
      exact TransCmp.lt_of_isLE_of_lt hc hkky

/-- Implementation detail of the tree map -/
def getEntryLT [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, compare a k = .lt) → (a : α) × β a
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => if hkky : compare k ky = .gt then
        getEntryLTD k r ⟨ky, y⟩
      else
        getEntryLT k l ho.left <| by
          obtain ⟨a, hm, hc⟩ := he
          refine ⟨a, ?_, hc⟩
          apply Ordered.mem_inner_iff_mem_left .. |>.mp hm
          apply TransCmp.lt_of_lt_of_isLE hc
          simpa [← Ordering.isLE_eq_false, Bool.not_eq_false] using hkky

/-- Implementation detail of the tree map -/
@[inline]
def getKeyGE? [Ord α] (k : α) : Impl α β → Option α :=
  go none
where
  go (best : Option α) : Impl α β → Option α
    | .leaf => best
    | .inner _ ky _ l r => match compare k ky with
      | .lt => go (some ky) l
      | .eq => some ky
      | .gt => go best r

/-- Implementation detail of the tree map -/
@[inline]
def getKeyGT? [Ord α] (k : α) : Impl α β → Option α :=
  go none
where
  go (best : Option α) : Impl α β → Option α
    | .leaf => best
    | .inner _ ky _ l r => match compare k ky with
      | .lt => go (some ky) l
      | _ => go best r

/-- Implementation detail of the tree map -/
@[inline]
def getKeyLE? [Ord α] (k : α) : Impl α β → Option α :=
  go none
where
  go (best : Option α) : Impl α β → Option α
    | .leaf => best
    | .inner _ ky _ l r => match compare k ky with
      | .lt => go best l
      | .eq => some ky
      | .gt => go (some ky) r

/-- Implementation detail of the tree map -/
@[inline]
def getKeyLT? [Ord α] (k : α) : Impl α β → Option α :=
  go none
where
  go (best : Option α) : Impl α β → Option α
    | .leaf => best
    | .inner _ ky _ l r => match compare k ky with
      | .gt => go (some ky) r
      | _ => go best l

/-- Implementation detail of the tree map -/
@[inline]
def getKeyGE! [Ord α] [Inhabited α] (k : α) (t : Impl α β) : α :=
  t.getKeyGE? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getKeyGT! [Ord α] [Inhabited α] (k : α) (t : Impl α β) : α :=
  t.getKeyGT? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getKeyLE! [Ord α] [Inhabited α] (k : α) (t : Impl α β) : α :=
  t.getKeyLE? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getKeyLT! [Ord α] [Inhabited α] (k : α) (t : Impl α β) : α :=
  t.getKeyLT? k |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getKeyGED [Ord α] (k : α) (t : Impl α β) (fallback : α) : α :=
  t.getKeyGE? k |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getKeyGTD [Ord α] (k : α) (t : Impl α β) (fallback : α) : α :=
  t.getKeyGT? k |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getKeyLED [Ord α] (k : α) (t : Impl α β) (fallback : α) : α :=
  t.getKeyLE? k |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getKeyLTD [Ord α] (k : α) (t : Impl α β) (fallback : α) : α :=
  t.getKeyLT? k |>.getD fallback

/-- Implementation detail of the tree map -/
def getKeyGE [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, (compare a k).isGE) → α
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => match hkky : compare k ky with
    | .lt => getKeyGED k l ky
    | .eq => ky
    | .gt => getKeyGE k r ho.right <| by
      obtain ⟨a, hm, hc⟩ := he
      refine ⟨a, ?_, hc⟩
      apply Ordered.mem_inner_iff_mem_right .. |>.mp hm
      exact TransCmp.gt_of_isGE_of_gt hc hkky

/-- Implementation detail of the tree map -/
def getKeyGT [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, compare a k = .gt) → α
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => if hkky : compare k ky = .lt then
        getKeyGTD k l ky
      else
        getKeyGT k r ho.right <| by
          obtain ⟨a, hm, hc⟩ := he
          refine ⟨a, ?_, hc⟩
          apply Ordered.mem_inner_iff_mem_right .. |>.mp hm
          apply TransCmp.gt_of_gt_of_isGE hc
          simpa [← Ordering.isGE_eq_false, Bool.not_eq_false] using hkky

/-- Implementation detail of the tree map -/
def getKeyLE [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, (compare a k).isLE) → α
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => match hkky : compare k ky with
    | .gt => getKeyLED k r ky
    | .eq => ky
    | .lt => getKeyLE k l ho.left <| by
      obtain ⟨a, hm, hc⟩ := he
      refine ⟨a, ?_, hc⟩
      apply Ordered.mem_inner_iff_mem_left .. |>.mp hm
      exact TransCmp.lt_of_isLE_of_lt hc hkky

/-- Implementation detail of the tree map -/
def getKeyLT [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, compare a k = .lt) → α
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => if hkky : compare k ky = .gt then
        getKeyLTD k r ky
      else
        getKeyLT k l ho.left <| by
          obtain ⟨a, hm, hc⟩ := he
          refine ⟨a, ?_, hc⟩
          apply Ordered.mem_inner_iff_mem_left .. |>.mp hm
          apply TransCmp.lt_of_lt_of_isLE hc
          simpa [← Ordering.isLE_eq_false, Bool.not_eq_false] using hkky

namespace Const

variable {β : Type v}

/-- Implementation detail of the tree map -/
def min? [Ord α] : Impl α β → Option (α × β)
  | .leaf => none
  | .inner _ k v .leaf _ => some ⟨k, v⟩
  | .inner _ _ _ l _ => min? l

/-- Implementation detail of the tree map -/
def min [Ord α] : (t : Impl α β) → (h : t.isEmpty = false) → α × β
  | .inner _ k v .leaf _, _ => ⟨k, v⟩
  | .inner _ _ _ l@(.inner _ _ _ _ _) _, h => min l (by simp_all [isEmpty])

/-- Implementation detail of the tree map -/
def min! [Ord α] [Inhabited (α × β)] : Impl α β → α × β
  | .leaf => panic! "Map is empty"
  | .inner _ k v .leaf _ => ⟨k, v⟩
  | .inner _ _ _ l _ => min! l

/-- Implementation detail of the tree map -/
def minD [Ord α] : Impl α β → α × β → α × β
  | .leaf, fallback => fallback
  | .inner _ k v .leaf _, _ => ⟨k, v⟩
  | .inner _ _ _ l _, fallback => minD l fallback

/-- Implementation detail of the tree map -/
def max? [Ord α] : Impl α β → Option (α × β)
  | .leaf => none
  | .inner _ k v _ .leaf => some ⟨k, v⟩
  | .inner _ _ _ _ r => max? r

/-- Implementation detail of the tree map -/
def max [Ord α] : (t : Impl α β) → (h : t.isEmpty = false) → α × β
  | .inner _ k v .leaf _, _ => ⟨k, v⟩
  | .inner _ _ _ l@(.inner _ _ _ _ _) _, h => max l (by simp_all [isEmpty])

/-- Implementation detail of the tree map -/
def max! [Ord α] [Inhabited (α × β)] : Impl α β → α × β
  | .leaf => panic! "Map is empty"
  | .inner _ k v _ .leaf => ⟨k, v⟩
  | .inner _ _ _ _ r => max! r

/-- Implementation detail of the tree map -/
def maxD [Ord α] : Impl α β → α × β → α × β
  | .leaf, fallback => fallback
  | .inner _ k v _ .leaf, _ => ⟨k, v⟩
  | .inner _ _ _ _ r, fallback => maxD r fallback

/-- Implementation detail of the tree map -/
@[inline]
def entryAtIdx [Ord α] : (t : Impl α β) → (hl : t.Balanced) → (n : Nat) → (h : n < t.size) → α × β
  | .inner _ k v l' r', hl, n, h =>
    match h : compare n l'.size with
    | .lt => entryAtIdx l' hl.left n (by simpa only [Std.Internal.tree_tac] using h)
    | .eq => ⟨k, v⟩
    | .gt =>
      entryAtIdx r' hl.right (n - l'.size - 1) (by simp_all only [Std.Internal.tree_tac]; omega)

/-- Implementation detail of the tree map -/
def entryAtIdx? [Ord α] : Impl α β → Nat → Option (α × β)
  | .leaf, _ => none
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => entryAtIdx? l n
    | .eq => some ⟨k, v⟩
    | .gt => entryAtIdx? r (n - l.size - 1)

/-- Implementation detail of the tree map -/
def entryAtIdx! [Ord α] [Inhabited (α × β)] : Impl α β → Nat → α × β
  | .leaf, _ => panic! "Out-of-bounds access"
  | .inner _ k v l r, n =>
    match compare n l.size with
    | .lt => entryAtIdx! l n
    | .eq => ⟨k, v⟩
    | .gt => entryAtIdx! r (n - l.size - 1)

/-- Implementation detail of the tree map -/
def entryAtIdxD [Ord α] : Impl α β → Nat → α × β → α × β
  | .leaf, _, fallback => fallback
  | .inner _ k v l r, n, fallback =>
    match compare n l.size with
    | .lt => entryAtIdxD l n fallback
    | .eq => ⟨k, v⟩
    | .gt => entryAtIdxD r (n - l.size - 1) fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGE? [Ord α] (k : α) : Impl α β → Option (α × β) :=
  go none
where
  go (best : Option (α × β)) : Impl α β → Option (α × β)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .lt => go (some ⟨ky, y⟩) l
      | .eq => some ⟨ky, y⟩
      | .gt => go best r

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGT? [Ord α] (k : α) : Impl α β → Option (α × β) :=
  go none
where
  go (best : Option (α × β)) : Impl α β → Option (α × β)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .lt => go (some ⟨ky, y⟩) l
      | _ => go best r

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLE? [Ord α] (k : α) : Impl α β → Option (α × β) :=
  go none
where
  go (best : Option (α × β)) : Impl α β → Option (α × β)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .lt => go best l
      | .eq => some ⟨ky, y⟩
      | .gt => go (some ⟨ky, y⟩) r

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLT? [Ord α] (k : α) : Impl α β → Option (α × β) :=
  go none
where
  go (best : Option (α × β)) : Impl α β → Option (α × β)
    | .leaf => best
    | .inner _ ky y l r => match compare k ky with
      | .gt => go (some ⟨ky, y⟩) r
      | _ => go best l

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGE! [Ord α] [Inhabited (α × β)] (k : α) (t : Impl α β) : α × β :=
  getEntryGE? k t |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGT! [Ord α] [Inhabited (α × β)] (k : α) (t : Impl α β) : α × β :=
  getEntryGT? k t |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLE! [Ord α] [Inhabited (α × β)] (k : α) (t : Impl α β) : α × β :=
  getEntryLE? k t |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLT! [Ord α] [Inhabited (α × β)] (k : α) (t : Impl α β) : α × β :=
  getEntryLT? k t |>.get!

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGED [Ord α] (k : α) (t : Impl α β) (fallback : α × β) : α × β :=
  getEntryGE? k t |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryGTD [Ord α] (k : α) (t : Impl α β) (fallback : α × β) : α × β :=
  getEntryGT? k t |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLED [Ord α] (k : α) (t : Impl α β) (fallback : α × β) : α × β :=
  getEntryLE? k t |>.getD fallback

/-- Implementation detail of the tree map -/
@[inline]
def getEntryLTD [Ord α] (k : α) (t : Impl α β) (fallback : α × β) : α × β :=
  getEntryLT? k t |>.getD fallback

/-- Implementation detail of the tree map -/
def getEntryGE [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, (compare a k).isGE) → α × β
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => match hkky : compare k ky with
    | .lt => getEntryGED k l ⟨ky, y⟩
    | .eq => ⟨ky, y⟩
    | .gt => getEntryGE k r ho.right <| by
      obtain ⟨a, hm, hc⟩ := he
      refine ⟨a, ?_, hc⟩
      apply Ordered.mem_inner_iff_mem_right .. |>.mp hm
      exact TransCmp.gt_of_isGE_of_gt hc hkky

/-- Implementation detail of the tree map -/
def getEntryGT [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, compare a k = .gt) → α × β
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => if hkky : compare k ky = .lt then
        getEntryGTD k l ⟨ky, y⟩
      else
        getEntryGT k r ho.right <| by
          obtain ⟨a, hm, hc⟩ := he
          refine ⟨a, ?_, hc⟩
          apply Ordered.mem_inner_iff_mem_right .. |>.mp hm
          apply TransCmp.gt_of_gt_of_isGE hc
          simpa [← Ordering.isGE_eq_false, Bool.not_eq_false] using hkky

/-- Implementation detail of the tree map -/
def getEntryLE [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, (compare a k).isLE) → α × β
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => match hkky : compare k ky with
    | .gt => getEntryLED k r ⟨ky, y⟩
    | .eq => ⟨ky, y⟩
    | .lt => getEntryLE k l ho.left <| by
      obtain ⟨a, hm, hc⟩ := he
      refine ⟨a, ?_, hc⟩
      apply Ordered.mem_inner_iff_mem_left .. |>.mp hm
      exact TransCmp.lt_of_isLE_of_lt hc hkky

/-- Implementation detail of the tree map -/
def getEntryLT [Ord α] [TransOrd α] (k : α) :
    (t : Impl α β) → (ho : t.Ordered) → (he : ∃ a ∈ t, compare a k = .lt) → α × β
  | .leaf, _, he => False.elim <| by obtain ⟨_, ha, _⟩ := he; cases ha
  | .inner _ ky y l r, ho, he => if hkky : compare k ky = .gt then
        getEntryLTD k r ⟨ky, y⟩
      else
        getEntryLT k l ho.left <| by
          obtain ⟨a, hm, hc⟩ := he
          refine ⟨a, ?_, hc⟩
          apply Ordered.mem_inner_iff_mem_left .. |>.mp hm
          apply TransCmp.lt_of_lt_of_isLE hc
          simpa [← Ordering.isLE_eq_false, Bool.not_eq_false] using hkky

end Const

end Std.DTreeMap.Internal.Impl
