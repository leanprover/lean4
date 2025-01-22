/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Orderedtree.Classes.LawfulEqOrd
import Orderedtree.DTreeMap.Internal.Impl.Attr
import Orderedtree.DTreeMap.Internal.Impl.Balancing
import Orderedtree.Classes.TransOrd

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

/-!
## `minView` and `maxView`
-/

variable (α β) in
/-- A tuple of a key-value pair and a tree. -/
structure RawView where
  /-- The key. -/
  k : α
  /-- The value. -/
  v : β k
  /-- The tree. -/
  tree : Impl α β

variable (α β) in
/-- A balanced tree of the given size. -/
structure Tree (size : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size `size`. -/
  size_impl : impl.size = size

variable (α β) in
/-- A tuple of a key-value pair and a balanced tree of size `size`. -/
structure View (size : Nat) where
  /-- The key. -/
  k : α
  /-- The value. -/
  v : β k
  /-- The tree. -/
  tree : Tree α β size

attribute [tree_tac] Tree.balanced_impl Tree.size_impl

/-- Returns the tree `l ++ ⟨k, v⟩ ++ r`, with the smallest element chopped off. -/
def minView (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hlr : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match l with
  | leaf => ⟨k, v, ⟨r, hr, ✓⟩⟩
  | inner _ k' v' l' r' =>
      let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := minView k' v' l' r' ✓ ✓ ✓
      ⟨dk, dv, ⟨balanceRErase k v dt r ✓ ✓ (by as_aux_lemma =>
        exact hlr.erase_left
          (by simp only [hdt', hl.eq, size_inner]; omega)
          (by simp only [hdt', hl.eq, size_inner]; omega)), ✓, ✓⟩⟩
  where triviality {n m : Nat} : n + 1 + m - 1 = n + m := by omega

/-- Slow version of `minView` which can be used in the absence of balance information but still
assumes the preconditions of `minView`, otherwise might panic. -/
def minViewSlow (k : α) (v : β k) (l r : Impl α β) : RawView α β :=
  match l with
  | leaf => ⟨k, v, r⟩
  | inner _ k' v' l' r' =>
      let d := minViewSlow k' v' l' r'
      ⟨d.k, d.v, balanceRSlow k v d.tree r⟩

/-- Returns the tree `l ++ ⟨k, v⟩ ++ r`, with the largest element chopped off. -/
def maxView (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced)
    (hlr : BalancedAtRoot l.size r.size) : View α β (l.size + r.size) :=
  match r with
  | leaf => ⟨k, v, ⟨l, hl, ✓⟩⟩
  | inner _ k' v' l' r' =>
      let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := maxView k' v' l' r' ✓ ✓ ✓
      ⟨dk, dv, ⟨balanceLErase k v l dt ✓ ✓ (by as_aux_lemma =>
        simp only [hdt', size_inner, hr.eq] at *
        apply hlr.erase_right <;> omega), ✓, ✓⟩⟩

/-- Slow version of `maxView` which can be used in the absence of balance information but still
assumes the preconditions of `maxView`, otherwise might panic. -/
def maxViewSlow (k : α) (v : β k) (l r : Impl α β) : RawView α β :=
  match r with
  | leaf => ⟨k, v, l⟩
  | inner _ k' v' l' r' =>
      let d := maxViewSlow k' v' l' r'
      ⟨d.k, d.v, balanceLSlow k v l d.tree⟩

/-!
## `glue`
-/

/-- Constructs the tree `l ++ r`. -/
@[inline]
def glue (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) (hlr : BalancedAtRoot l.size r.size) :
    Impl α β :=
  match l with
  | .leaf => r
  | .inner sz k v l' r' =>
    match r with
    | .leaf => l
    | .inner sz' k' v' l'' r'' =>
      if sz < sz' then
        let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := minView k' v' l'' r'' ✓ ✓ ✓
        balanceLErase dk dv (.inner sz k v l' r') dt hl ✓
          (by as_aux_lemma =>
            simp only [hdt', size_inner, hr.eq] at *
            apply hlr.erase_right <;> omega)
      else
        let ⟨dk, dv, ⟨dt, hdt, hdt'⟩⟩ := maxView k v l' r' ✓ ✓ ✓
        balanceRErase dk dv dt (.inner sz' k' v' l'' r'') ✓ hr
          (by as_aux_lemma =>
            simp only [hdt', size_inner, hl.eq] at *
            apply hlr.erase_left <;> omega)

@[tree_tac]
theorem size_glue {l r : Impl α β} {hl hr hlr} : (glue l r hl hr hlr).size = l.size + r.size := by
  simp only [glue]; tree_tac

@[tree_tac]
theorem balanced_glue {l r : Impl α β} {hl hr hlr} : (glue l r hl hr hlr).Balanced := by
  simp only [glue]; tree_tac

/-- Slower version of `glue` which can be used in the absence of balance information but still
assumes the preconditions of `glue`, otherwise might panic. -/
@[inline]
def glueSlow (l r : Impl α β) : Impl α β :=
  match l with
  | .leaf => r
  | l@(.inner sz k v l' r') =>
    match r with
    | .leaf => l
    | r@(.inner sz' k' v' l'' r'') =>
      if sz < sz' then
        let d := minViewSlow k' v' l'' r''
        balanceLSlow d.k d.v l d.tree
      else
        let d := maxViewSlow k v l' r'
        balanceRSlow d.k d.v d.tree r

/-!
## `insertMin` and `insertMax`
-/

/-- Inserts an element at the beginning of the tree. -/
def insertMin (k : α) (v : β k) (t : Impl α β) (hr : t.Balanced) : Tree α β (1 + t.size) :=
  match t with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | inner sz k' v' l' r' =>
      let ⟨l'', hl''₁, hl''₂⟩ := insertMin k v l' ✓
      ⟨balanceL k' v' l'' r' ✓ ✓ ✓, ✓, ✓⟩

/-- Slower version of `insertMin` which can be used in the absence of balance information but
still assumes the preconditions of `insertMin`, otherwise might panic. -/
def insertMinSlow (k : α) (v : β k) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .inner 1 k v .leaf .leaf
  | inner _ k' v' l' r' => balanceLSlow k' v' (insertMinSlow k v l') r'

/-- Inserts an element at the end of the tree. -/
def insertMax (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) : Tree α β (t.size + 1) :=
  match t with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | inner sz k' v' l' r' =>
      let ⟨r'', hr''₁, hr''₂⟩ := insertMax k v r' ✓
      ⟨balanceR k' v' l' r'' ✓ ✓ ✓, ✓, ✓⟩

/-- Slower version of `insertMax` which can be used in the absence of balance information but
still assumes the preconditions of `insertMax`, otherwise might panic. -/
def insertMaxSlow (k : α) (v : β k) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .inner 1 k v .leaf .leaf
  | inner _ k' v' l' r' => balanceRSlow k' v' l' (insertMaxSlow k v r')

/-!
## `link` and `link2`
-/

attribute [tree_tac] and_true true_and

/-- Builds the tree `l ++ ⟨k, v⟩ ++ r` without any balancing information at the root. -/
def link (k : α) (v : β k) (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) :
    Tree α β (l.size + 1 + r.size) :=
  match l with
  | leaf =>
      let d := insertMin k v r ✓
      ⟨d.impl, ✓, ✓⟩
  | (inner szl k' v' l' r') =>
      match r with
      | leaf =>
          let d := insertMax k v (inner szl k' v' l' r') ✓
          ⟨d.impl, ✓, ✓⟩
      | (inner szr k'' v'' l'' r'') =>
          if h₁ : delta * szl < szr then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link k v (inner szl k' v' l' r') l'' ✓ ✓
            ⟨balanceLErase k'' v'' ℓ r'' ✓ ✓ ✓, ✓, ✓⟩
          else if h₂ : delta * szr < szl then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link k v r' (inner szr k'' v'' l'' r'') ✓ ✓
            ⟨balanceRErase k' v' l' ℓ ✓ ✓ ✓, ✓, ✓⟩
          else
            ⟨.inner (szl + 1 + szr) k v (inner szl k' v' l' r') (inner szr k'' v'' l'' r''),
              ✓, ✓⟩
  termination_by sizeOf l + sizeOf r

/-- Slower version of `link` which can be used in the absence of balance information but
still assumes the preconditions of `link`, otherwise might panic. -/
def linkSlow (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => insertMinSlow k v r
  | l@(inner szl k' v' l' r') =>
      match r with
      | leaf => insertMaxSlow k v l
      | r@(inner szr k'' v'' l'' r'') =>
          if delta * szl < szr then
            balanceLSlow k'' v'' (linkSlow k v l l'') r''
          else if delta * szr < szl then
            balanceRSlow k' v' l' (linkSlow k v r r')
          else
            .inner (l.size + 1 + r.size) k v l r
  termination_by sizeOf l + sizeOf r

/-- Builds the tree `l ++ r` without any balancing information at the root. -/
def link2 (l r : Impl α β) (hl : l.Balanced) (hr : r.Balanced) :
    Tree α β (l.size + r.size) :=
  match hl' : l with
  | leaf => ⟨r, ✓, ✓⟩
  | (inner szl k' v' l' r') =>
      match hr' : r with
      | leaf => ⟨l, ✓, ✓⟩
      | (inner szr k'' v'' l'' r'') =>
          if h₁ : delta * szl < szr then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link2 l l'' ✓ ✓
            ⟨balanceLErase k'' v'' ℓ r'' ✓ ✓ ✓, ✓, ✓⟩
          else if h₂ : delta * szr < szl then
            let ⟨ℓ, hℓ₁, hℓ₂⟩ := link2 r' r ✓ ✓
            ⟨balanceRErase k' v' l' ℓ ✓ ✓ ✓, ✓, ✓⟩
          else
            ⟨glue l r ✓ ✓ ✓, ✓, ✓⟩
  termination_by sizeOf l + sizeOf r

/-- Slower version of `link2` which can be used in the absence of balance information but
still assumes the preconditions of `link2`, otherwise might panic. -/
def link2Slow (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => r
  | l@(inner szl k' v' l' r') =>
      match r with
      | leaf => l
      | r@(inner szr k'' v'' l'' r'') =>
          if delta * szl < szr then
            balanceLSlow k'' v'' (link2Slow l l'') r''
          else if delta * szr < szl then
            balanceRSlow k' v' l' (link2Slow r' r )
          else
            glueSlow l r
  termination_by sizeOf l + sizeOf r

/-!
## Modification operations
-/


-- TODO: inline annotations
-- TODO: rename slow to !

variable (α β) in
/-- A balanced tree of one of the given sizes. -/
structure TreeB (lb ub : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size at least `lb`. -/
  lb_le_size_impl : lb ≤ impl.size
  /-- The tree has size at most `ub`. -/
  size_impl_le_ub : impl.size ≤ ub

attribute [tree_tac] TreeB.balanced_impl

/-- An empty tree. -/
@[inline]
def empty : Impl α β :=
  .leaf

@[tree_tac]
theorem balanced_empty : (empty : Impl α β).Balanced :=
  .leaf

attribute [tree_tac] or_true true_or

/-- Adds a new mapping to the key, overwriting an existing one with equal key if present. -/
def insert [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    TreeB α β t.size (t.size + 1) :=
  match t with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓, ✓⟩
  | inner sz k' v' l' r' =>
      match compare k k' with
      | .lt =>
          let ⟨d, hd, hd₁, hd₂⟩ := insert k v l' ✓
          ⟨balanceL k' v' d r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | .gt =>
          let ⟨d, hd, hd₁, hd₂⟩ := insert k v r' ✓
          ⟨balanceR k' v' l' d ✓ ✓ ✓, ✓, ✓, ✓⟩
      | .eq => ⟨.inner sz k v l' r', ✓, ✓, ✓⟩

/-- Slower version of `insert` which can be used in the absence of balance information but
still assumes the preconditions of `insert`, otherwise might panic. -/
def insertSlow [Ord α] (k : α) (v : β k) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .inner 1 k v .leaf .leaf
  | inner sz k' v' l r =>
      match compare k k' with
      | .lt => balanceLSlow k' v' (insertSlow k v l) r
      | .gt => balanceRSlow k' v' l (insertSlow k v r)
      | .eq => .inner sz k v l r

/-- Returns the pair `(t.contains k, t.insert k v)`. -/
@[inline]
def containsThenInsert [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    Bool × TreeB α β t.size (t.size + 1) :=
  let sz := size t
  let m := t.insert k v hl
  (sz == m.1.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

/-- Slower version of `containsThenInsert` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsert`, otherwise might panic. -/
@[inline]
def containsThenInsertSlow [Ord α] (k : α) (v : β k) (t : Impl α β) :
    Bool × Impl α β :=
  let sz := size t
  let m := t.insertSlow k v
  (sz == m.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

/-- Adds a new mapping to the key, overwriting an existing one with equal key if present. -/
@[inline]
def insertIfNew [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    TreeB α β t.size (t.size + 1) :=
  if t.contains k then ⟨t, ✓, ✓, ✓⟩ else t.insert k v ✓

/-- Slower version of `insertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `insertIfNew`, otherwise might panic. -/
@[inline]
def insertIfNewSlow [Ord α] (k : α) (v : β k) (t : Impl α β) :
    Impl α β :=
  if t.contains k then t else t.insertSlow k v

/-- Returns the pair `(t.contains k, t.insertIfNew k v)`. -/
@[inline]
def containsThenInsertIfNew [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    Bool × TreeB α β t.size (t.size + 1) :=
  if t.contains k then (true, ⟨t, ✓, ✓, ✓⟩) else (false, t.insert k v ✓)

/-- Slower version of `containsThenInsertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsertIfNew`, otherwise might panic. -/
@[inline]
def containsThenInsertIfNewSlow [Ord α] (k : α) (v : β k) (t : Impl α β) :
    Bool × Impl α β :=
  if t.contains k then (true, t) else (false, t.insertSlow k v)

/-- Returns the pair `(t.get? k, t.insertIfNew k v)`. -/
@[inline]
def getThenInsertIfNew? [Ord α] [LawfulEqOrd α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    Option (β k) × Impl α β :=
  match t.get? k with
  | some v' => (some v', t)
  | none => (none, (t.insertIfNew k v hl).impl)

/-- Slower version of `getThenInsertIfNew?` which can be used in the absence of balance
information but still assumes the preconditions of `getThenInsertIfNew?`, otherwise might panic. -/
@[inline]
def getThenInsertIfNewSlow? [Ord α] [LawfulEqOrd α] (k : α) (v : β k) (t : Impl α β) :
    Option (β k) × Impl α β :=
  match t.get? k with
  | some v' => (some v', t)
  | none => (none, t.insertIfNewSlow k v)

namespace Const

/-- Returns the pair `(t.get? k, t.insertIfNew k v)`. -/
@[inline]
def getThenInsertIfNew? [Ord α] (k : α) (v : δ) (t : Impl α (fun _ => δ)) (hl : t.Balanced) :
    Option δ × Impl α (fun _ => δ) :=
  match Const.get? k t with
  | some v' => (some v', t)
  | none => (none, (t.insertIfNew k v hl).impl)

/-- Slower version of `getThenInsertIfNew?` which can be used in the absence of balance
information but still assumes the preconditions of `getThenInsertIfNew?`, otherwise might panic. -/
@[inline]
def getThenInsertIfNewSlow? [Ord α] (k : α) (v : δ) (t : Impl α (fun _ => δ)) :
    Option δ × Impl α (fun _ => δ) :=
  match Const.get? k t with
  | some v' => (some v', t)
  | none => (none, t.insertIfNewSlow k v)

end Const

/-- Removes the mapping with key `k`, if it exists. -/
def erase [Ord α] (t : Impl α β) (k : α) (h : t.Balanced) : TreeB α β (t.size - 1) t.size :=
  match t with
  | leaf => ⟨.leaf, ✓, ✓, ✓⟩
  | inner sz k' v' l r =>
    match compare k k' with
    | .lt =>
      let ⟨l', hl'₁, hl'₂, hl'₃⟩ := erase l k ✓
      ⟨balanceRErase k' v' l' r ✓ ✓ ✓, ✓, ✓, ✓⟩
    | .gt =>
      let ⟨r', hr'₁, hr'₂, hr'₃⟩ := erase r k ✓
      ⟨balanceLErase k' v' l r' ✓ ✓ ✓, ✓, ✓, ✓⟩
    | .eq => ⟨glue l r ✓ ✓ ✓, ✓, ✓, ✓⟩

/-- Slower version of `erase` which can be used in the absence of balance
information but still assumes the preconditions of `erase`, otherwise might panic. -/
def eraseSlow [Ord α] (t : Impl α β) (k : α) : Impl α β :=
  match t with
  | leaf => .leaf
  | inner _ k' v' l r =>
    match compare k k' with
    | .lt => balanceRSlow k' v' (eraseSlow l k) r
    | .gt => balanceLSlow k' v' l (eraseSlow r k)
    | .eq => glueSlow l r

variable (α β) in
/-- A balanced tree. -/
structure BImpl where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced

attribute [tree_tac] BImpl.balanced_impl

/-- Returns the tree consisting of the mappings `(k, (f k v).get)` where `(k, v)` was a mapping in
the original tree and `(f k v).isSome`. -/
@[specialize]
def filterMap [Ord α] (f : (a : α) → β a → Option (γ a)) (t : Impl α β) (hl : t.Balanced) :
    BImpl α γ :=
  match t with
  | .leaf => ⟨.leaf, ✓⟩
  | .inner sz k v l r =>
    match f k v with
    | none =>
        let ⟨l', hl'⟩ := filterMap f l ✓
        let ⟨r', hr'⟩ := filterMap f r ✓
        ⟨(link2 l' r' ✓ ✓).impl, ✓⟩
    | some v' =>
        let ⟨l', hl'⟩ := filterMap f l ✓
        let ⟨r', hr'⟩ := filterMap f r ✓
        ⟨(link k v' l' r' ✓ ✓).impl, ✓⟩

/-- Slower version of `filterMap` which can be used in the absence of balance
information but still assumes the preconditions of `filterMap`, otherwise might panic. -/
@[specialize]
def filterMapSlow [Ord α] (f : (a : α) → β a → Option (γ a)) (t : Impl α β) : Impl α γ :=
  match t with
  | .leaf => .leaf
  | .inner _ k v l r =>
    match f k v with
    | none => link2Slow (filterMapSlow f l) (filterMapSlow f r)
    | some v' => linkSlow k v' (filterMapSlow f l) (filterMapSlow f r)

/-- Returns the tree consisting of the mappings `(k, f k v)` where `(k, v)` was a mapping in the
original tree. -/
@[specialize]
def map [Ord α] (f : (a : α) → β a → γ a) (t : Impl α β) : Impl α γ :=
  match t with
  | .leaf => .leaf
  | .inner sz k v l r => .inner sz k (f k v) (map f l) (map f r)

/-- Returns the tree consisting of the mapping `(k, v)` where `(k, v)` was a mapping in the
original tree and `f k v = true`. -/
@[specialize]
def filter [Ord α] (f : (a : α) → β a → Bool) (t : Impl α β) (hl : Balanced t) : BImpl α β :=
  match t with
  | .leaf => ⟨.leaf, ✓⟩
  | .inner sz k v l r =>
    match f k v with
    | false =>
        let ⟨l', hl'⟩ := filter f l ✓
        let ⟨r', hr'⟩ := filter f r ✓
        ⟨(link2 l' r'  ✓ ✓).impl, ✓⟩
    | true =>
        let ⟨l', hl'⟩ := filter f l ✓
        let ⟨r', hr'⟩ := filter f r ✓
        ⟨(link k v l' r' ✓ ✓).impl, ✓⟩

/-- Slower version of `filter` which can be used in the absence of balance
information but still assumes the preconditions of `filter`, otherwise might panic. -/
@[specialize]
def filterSlow [Ord α] (f : (a : α) → β a → Bool) (t : Impl α β) : Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner _ k v l r =>
    match f k v with
    | false => link2Slow (filterSlow f l) (filterSlow f r)
    | true => linkSlow k v (filterSlow f l) (filterSlow f r)

namespace Const

-- TODO: unify indentation

/-- Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it. -/
@[specialize]
def alter [Ord α] (k : α) (f : Option δ → Option δ) (t : Impl α (fun _ => δ)) (hl : t.Balanced) :
    TreeB α (fun _ => δ) (t.size - 1) (t.size + 1) :=
  match t with
  | .leaf =>
    match f none with
    | none => ⟨.leaf, ✓, ✓, ✓⟩
    | some v => ⟨.inner 1 k v .leaf .leaf, ✓, ✓, ✓⟩
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f l' ✓
        ⟨balance k' v' d r' ✓ ✓ (hl.at_root.adjust_left hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .gt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f r' ✓
        ⟨balance k' v' l' d ✓ ✓ (hl.at_root.adjust_right hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .eq =>
      match f (some v') with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k' v l' r', ✓, ✓, ✓⟩

/-- Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic. -/
@[specialize]
def alterSlow [Ord α] (k : α) (f : Option δ → Option δ) (t : Impl α (fun _ => δ)) :
    Impl α (fun _ => δ) :=
  match t with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt => balanceSlow k' v' (alterSlow k f l') r'
    | .gt => balanceSlow k' v' l' (alterSlow k f r')
    | .eq =>
      match f (some v') with
      | none => glueSlow l' r'
      | some v => .inner sz k' v l' r'

end Const

/-- Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it.
This version of the function requires `LawfulEqOrd α`. There is an alternative non-dependent version
called `Const.modify`. -/
@[specialize]
def alter [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (t : Impl α β)
    (hl : t.Balanced) : TreeB α β (t.size - 1) (t.size + 1) :=
  match t with
  | .leaf =>
    match f none with
    | none => ⟨.leaf, ✓, ✓, ✓⟩
    | some v => ⟨.inner 1 k v .leaf .leaf, ✓, ✓, ✓⟩
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f l' ✓
        ⟨balance k' v' d r' ✓ ✓ (hl.at_root.adjust_left hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .gt =>
        let ⟨d, hd, hd'₁, hd'₂⟩ := alter k f r' ✓
        ⟨balance k' v' l' d ✓ ✓ (hl.at_root.adjust_right hd'₁ hd'₂), ✓, ✓, ✓⟩
    | .eq =>
      match f (some (cast (congrArg β (eq_of_compare h).symm) v')) with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k v l' r', ✓, ✓, ✓⟩

/-- Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic. -/
@[specialize]
def alterSlow [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (t : Impl α β) :
    Impl α β :=
  match t with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt => balanceSlow k' v' (alterSlow k f l') r'
    | .gt => balanceSlow k' v' l' (alterSlow k f r')
    | .eq =>
      match f (some (cast (congrArg β (eq_of_compare h).symm) v')) with
      | none => glueSlow l' r'
      | some v => .inner sz k v l' r'

/-- If the tree contains a mapping `(k', v)` with `k == k'`, adjust it to have mapping
`(k', f k' v h)`, which `h : compare k k' = .eq`. If no such mapping is present, returns the
tree unmodified. Note that this function is likely to be faster than `modify` because it never
needs to rebalance the tree. -/
def modify [Ord α] (k : α) (f : (k' : α) → β k' → (compare k k' = .eq) → β k') (t : Impl α β) :
    Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k' v' l r =>
    match h : compare k k' with
    | .lt => .inner sz k' v' (modify k f l) r
    | .gt => .inner sz k' v' l (modify k f r)
    | .eq => .inner sz k' (f k' v' h) l r

attribute [tree_tac] Nat.compare_eq_gt Nat.compare_eq_lt Nat.compare_eq_eq

/-- Returns the mapping with the `n`-th smallest key. -/
def atIndex [Ord α] : (t : Impl α β) → (hl : t.Balanced) → (n : Nat) → (h : n < t.size) → (a : α) × β a
  | .inner _ k v l' r', hl, n, h =>
    match h : compare n l'.size with
    | .lt => l'.atIndex hl.left n ✓
    | .eq => ⟨k, v⟩
    | .gt => r'.atIndex hl.right (n - l'.size - 1) ✓

/-- Folds the given function over the mappings in the tree in ascending order. -/
@[specialize]
def foldlM [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ) : Impl α β → m δ
  | .leaf => pure init
  | .inner _ k v l r => do
    let left ← foldlM f init l
    let middle ← f left k v
    foldlM f middle r

/-- Folds the given function over the mappings in the tree in ascending order. -/
@[inline]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : Impl α β) : δ :=
  Id.run (t.foldlM f init)

/-- Applies the given function to the mappings in the tree in ascending order. -/
@[inline]
def forM [Monad m] (f : (a : α) → β a → m PUnit) (t : Impl α β) : m PUnit :=
  t.foldlM (fun _ k v => f k v) ⟨⟩

/-- Implementation detail. -/
@[specialize]
def forInStep [Monad m] (f : δ → (a : α) → β a → m (ForInStep δ)) (init : δ) :
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
def forIn [Monad m] (f : δ → (a : α) → β a → m (ForInStep δ)) (init : δ) (t : Impl α β) : m δ := do
  match ← forInStep f init t with
  | ForInStep.done d => return d
  | ForInStep.yield d => return d
