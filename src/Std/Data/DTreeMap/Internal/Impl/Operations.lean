/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.Classes.LawfulEqOrd
import Std.Data.DTreeMap.Internal.Impl.Balancing
import Std.Data.Classes.TransOrd

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

open Lean.Parser.Tactic

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

variable (α β) in
/-- A balanced tree. -/
structure BImpl where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced

attribute [tree_tac] BImpl.balanced_impl
