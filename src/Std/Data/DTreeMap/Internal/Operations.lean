/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
module

prelude
public import Init.Data.Nat.Compare
public import Std.Data.DTreeMap.Internal.Balancing
public import Std.Data.DTreeMap.Internal.Queries
public import Init.Data.Order.Ord

@[expose] public section

/-!
# Low-level implementation of the size-bounded tree

This file contains the basic definition implementing the functionality of the size-bounded trees.
-/

set_option autoImplicit false
set_option linter.all true

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type w}

namespace Std.DTreeMap.Internal.Impl

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

attribute [Std.Internal.tree_tac] Tree.balanced_impl Tree.size_impl

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

/--
Slower version of `minView` which can be used in the absence of balance information but still
assumes the preconditions of `minView`, otherwise might panic.
-/
def minView! (k : α) (v : β k) (l r : Impl α β) : RawView α β :=
  match l with
  | leaf => ⟨k, v, r⟩
  | inner _ k' v' l' r' =>
    let d := minView! k' v' l' r'
    ⟨d.k, d.v, balanceR! k v d.tree r⟩

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

/--
Slower version of `maxView` which can be used in the absence of balance information but still
assumes the preconditions of `maxView`, otherwise might panic.
-/
def maxView! (k : α) (v : β k) (l r : Impl α β) : RawView α β :=
  match r with
  | leaf => ⟨k, v, l⟩
  | inner _ k' v' l' r' =>
    let d := maxView! k' v' l' r'
    ⟨d.k, d.v, balanceL! k v l d.tree⟩

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

@[Std.Internal.tree_tac]
theorem size_glue {l r : Impl α β} {hl hr hlr} : (glue l r hl hr hlr).size = l.size + r.size := by
  simp only [glue]; tree_tac

@[Std.Internal.tree_tac]
theorem balanced_glue {l r : Impl α β} {hl hr hlr} : (glue l r hl hr hlr).Balanced := by
  simp only [glue]; tree_tac

/--
Slower version of `glue` which can be used in the absence of balance information but still
assumes the preconditions of `glue`, otherwise might panic.
-/
@[inline]
def glue! (l r : Impl α β) : Impl α β :=
  match l with
  | .leaf => r
  | l@(.inner sz k v l' r') =>
    match r with
    | .leaf => l
    | r@(.inner sz' k' v' l'' r'') =>
      if sz < sz' then
        let d := minView! k' v' l'' r''
        balanceL! d.k d.v l d.tree
      else
        let d := maxView! k v l' r'
        balanceR! d.k d.v d.tree r

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

/--
Slower version of `insertMin` which can be used in the absence of balance information but
still assumes the preconditions of `insertMin`, otherwise might panic.
-/
def insertMin! (k : α) (v : β k) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .inner 1 k v .leaf .leaf
  | inner _ k' v' l' r' => balanceL! k' v' (insertMin! k v l') r'

/-- Inserts an element at the end of the tree. -/
def insertMax (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) : Tree α β (t.size + 1) :=
  match t with
  | leaf => ⟨.inner 1 k v .leaf .leaf, ✓, ✓⟩
  | inner sz k' v' l' r' =>
    let ⟨r'', hr''₁, hr''₂⟩ := insertMax k v r' ✓
    ⟨balanceR k' v' l' r'' ✓ ✓ ✓, ✓, ✓⟩

/--
Slower version of `insertMax` which can be used in the absence of balance information but
still assumes the preconditions of `insertMax`, otherwise might panic.
-/
def insertMax! (k : α) (v : β k) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .inner 1 k v .leaf .leaf
  | inner _ k' v' l' r' => balanceR! k' v' l' (insertMax! k v r')

/-!
## `link` and `link2`
-/

attribute [Std.Internal.tree_tac] and_true true_and

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

/--
Slower version of `link` which can be used in the absence of balance information but
still assumes the preconditions of `link`, otherwise might panic.
-/
def link! (k : α) (v : β k) (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => insertMin! k v r
  | l@(inner szl k' v' l' r') =>
    match r with
    | leaf => insertMax! k v l
    | r@(inner szr k'' v'' l'' r'') =>
      if delta * szl < szr then
        balanceL! k'' v'' (link! k v l l'') r''
      else if delta * szr < szl then
        balanceR! k' v' l' (link! k v r' r)
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
still assumes the preconditions of `link2`, otherwise might panic.
-/
def link2! (l r : Impl α β) : Impl α β :=
  match l with
  | leaf => r
  | l@(inner szl k' v' l' r') =>
    match r with
    | leaf => l
    | r@(inner szr k'' v'' l'' r'') =>
      if delta * szl < szr then
        balanceL! k'' v'' (link2! l l'') r''
      else if delta * szr < szl then
        balanceR! k' v' l' (link2! r' r )
      else
        glue! l r
termination_by sizeOf l + sizeOf r

/-!
## Modification operations
-/

variable (α β) in
/-- A balanced tree of one of the given sizes. -/
structure SizedBalancedTree (lb ub : Nat) where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced
  /-- The tree has size at least `lb`. -/
  lb_le_size_impl : lb ≤ impl.size
  /-- The tree has size at most `ub`. -/
  size_impl_le_ub : impl.size ≤ ub

attribute [Std.Internal.tree_tac] SizedBalancedTree.balanced_impl

/-- An empty tree. -/
@[inline]
def empty : Impl α β :=
  .leaf

@[Std.Internal.tree_tac]
theorem balanced_empty : (empty : Impl α β).Balanced :=
  .leaf

attribute [Std.Internal.tree_tac] or_true true_or

/-- Adds a new mapping to the key, overwriting an existing one with equal key if present. -/
def insert [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    SizedBalancedTree α β t.size (t.size + 1) :=
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

/--
Slower version of `insert` which can be used in the absence of balance information but
still assumes the preconditions of `insert`, otherwise might panic.
-/
def insert! [Ord α] (k : α) (v : β k) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .inner 1 k v .leaf .leaf
  | inner sz k' v' l r =>
    match compare k k' with
    | .lt => balanceL! k' v' (insert! k v l) r
    | .gt => balanceR! k' v' l (insert! k v r)
    | .eq => .inner sz k v l r

/-- Returns the pair `(t.contains k, t.insert k v)`. -/
@[inline]
def containsThenInsert [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    Bool × SizedBalancedTree α β t.size (t.size + 1) :=
  let sz := size t
  let m := t.insert k v hl
  (sz == m.1.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

/--
Slower version of `containsThenInsert` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsert`, otherwise might panic.
-/
@[inline]
def containsThenInsert! [Ord α] (k : α) (v : β k) (t : Impl α β) :
    Bool × Impl α β :=
  let sz := size t
  let m := t.insert! k v
  (sz == m.size, m)
where -- workaround for https://github.com/leanprover/lean4/issues/6058
  size : Impl α β → Nat
  | leaf => 0
  | inner sz _ _ _ _ => sz

/-- Adds a new mapping to the tree, leaving the tree unchanged if the key is already present. -/
@[inline]
def insertIfNew [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    SizedBalancedTree α β t.size (t.size + 1) :=
  if t.contains k then ⟨t, ✓, ✓, ✓⟩ else t.insert k v ✓

/--
Slower version of `insertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `insertIfNew`, otherwise might panic.
-/
@[inline]
def insertIfNew! [Ord α] (k : α) (v : β k) (t : Impl α β) :
    Impl α β :=
  if t.contains k then t else t.insert! k v

/-- Returns the pair `(t.contains k, t.insertIfNew k v)`. -/
@[inline]
def containsThenInsertIfNew [Ord α] (k : α) (v : β k) (t : Impl α β) (hl : t.Balanced) :
    Bool × SizedBalancedTree α β t.size (t.size + 1) :=
  if t.contains k then (true, ⟨t, ✓, ✓, ✓⟩) else (false, t.insert k v ✓)

/--
Slower version of `containsThenInsertIfNew` which can be used in the absence of balance
information but still assumes the preconditions of `containsThenInsertIfNew`, otherwise might panic.
-/
@[inline]
def containsThenInsertIfNew! [Ord α] (k : α) (v : β k) (t : Impl α β) :
    Bool × Impl α β :=
  if t.contains k then (true, t) else (false, t.insert! k v)

/-- Implementation detail of the tree map -/
@[inline]
def getThenInsertIfNew? [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) (v : β k) (ht : t.Balanced) :
    Option (β k) × Impl α β :=
  match t.get? k with
  | none => (none, t.insertIfNew k v ht |>.impl)
  | some b => (some b, t)

/--
Slower version of `getThenInsertIfNew?` which can be used in the absence of balance
information but still assumes the preconditions of `getThenInsertIfNew?`, otherwise might panic.
-/
@[inline]
def getThenInsertIfNew?! [Ord α] [LawfulEqOrd α] (t : Impl α β) (k : α) (v : β k) :
    Option (β k) × Impl α β :=
  match t.get? k with
  | none => (none, t.insertIfNew! k v)
  | some b => (some b, t)

/-- Removes the mapping with key `k`, if it exists. -/
def erase [Ord α] (k : α) (t : Impl α β) (h : t.Balanced) :
    SizedBalancedTree α β (t.size - 1) t.size :=
  match t with
  | leaf => ⟨.leaf, ✓, ✓, ✓⟩
  | inner sz k' v' l r =>
    match compare k k' with
    | .lt =>
      let ⟨l', hl'₁, hl'₂, hl'₃⟩ := erase k l ✓
      ⟨balanceRErase k' v' l' r ✓ ✓ ✓, ✓, ✓, ✓⟩
    | .gt =>
      let ⟨r', hr'₁, hr'₂, hr'₃⟩ := erase k r ✓
      ⟨balanceLErase k' v' l r' ✓ ✓ ✓, ✓, ✓, ✓⟩
    | .eq => ⟨glue l r ✓ ✓ ✓, ✓, ✓, ✓⟩

/--
Slower version of `erase` which can be used in the absence of balance
information but still assumes the preconditions of `erase`, otherwise might panic.
-/
def erase! [Ord α] (k : α) (t : Impl α β) : Impl α β :=
  match t with
  | leaf => .leaf
  | inner _ k' v' l r =>
    match compare k k' with
    | .lt => balanceR! k' v' (erase! k l) r
    | .gt => balanceL! k' v' l (erase! k r)
    | .eq => glue! l r

/-- A tree map obtained by erasing elements from `t`, bundled with an inductive principle. -/
abbrev IteratedErasureFrom [Ord α] (t) :=
  { t' // ∀ {P : Impl α β → Prop}, P t → (∀ t'' a h, P t'' → P (t''.erase a h).impl) → P t' }

/-- Iterate over `l` and erase all of its elements from `t`. -/
@[inline]
def eraseMany [Ord α] {ρ : Type w} [ForIn Id ρ α] (t : Impl α β) (l : ρ) (h : t.Balanced) :
    IteratedErasureFrom t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for a in l do
    let hr := r.2 h (fun t'' a h _ => (t''.erase a h).balanced_impl)
    r := ⟨r.val.erase a hr |>.impl, fun h₀ h₁ => h₁ _ _ _ (r.2 h₀ h₁)⟩
  return r

/-- A tree map obtained by erasing elements from `t`, bundled with an inductive principle. -/
abbrev IteratedSlowErasureFrom [Ord α] (t) :=
  { t' // ∀ {P : Impl α β → Prop}, P t → (∀ t'' a, P t'' → P (t''.erase! a)) → P t' }

/--
Slower version of `eraseMany` which can be used in absence of balance information but still
assumes the preconditions of `eraseMany`, otherwise might panic.
-/
@[inline]
def eraseMany! [Ord α] {ρ : Type w} [ForIn Id ρ α] (t : Impl α β) (l : ρ) :
    IteratedSlowErasureFrom t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for a in l do
    r := ⟨r.val.erase! a, fun h₀ h₁ => h₁ _ _ (r.2 h₀ h₁)⟩
  return r

/-- A tree map obtained by inserting elements into `t`, bundled with an inductive principle. -/
abbrev IteratedInsertionInto [Ord α] (t) :=
  { t' // ∀ {P : Impl α β → Prop}, P t → (∀ t'' a b h, P t'' → P (t''.insert a b h).impl) → P t' }

/-- Iterate over `l` and insert all of its elements into `t`. -/
@[inline]
def insertMany [Ord α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (t : Impl α β) (l : ρ) (h : t.Balanced) :
    IteratedInsertionInto t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for ⟨a, b⟩ in l do
    let hr := r.2 h (fun t'' a b h _ => (t''.insert a b h).balanced_impl)
    r := ⟨r.val.insert a b hr |>.impl, fun h₀ h₁ => h₁ _ _ _ _ (r.2 h₀ h₁)⟩
  return r

/-- A tree map obtained by inserting elements into `t`, bundled with an inductive principle. -/
abbrev IteratedSlowInsertionInto [Ord α] (t) :=
  { t' // ∀ {P : Impl α β → Prop}, P t → (∀ t'' a b, P t'' → P (t''.insert! a b)) → P t' }

/--
Slower version of `insertMany` which can be used in absence of balance information but still
assumes the preconditions of `insertMany`, otherwise might panic.
-/
@[inline]
def insertMany! [Ord α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (t : Impl α β) (l : ρ) :
    IteratedSlowInsertionInto t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for ⟨a, b⟩ in l do
    r := ⟨r.val.insert! a b, fun h₀ h₁ => h₁ _ _ _ (r.2 h₀ h₁)⟩
  return r

namespace Const

variable {β : Type v}

/-- A tree map obtained by inserting elements into `t`, bundled with an inductive principle. -/
abbrev IteratedInsertionInto [Ord α] (t) :=
  { t' // ∀ {P : Impl α (fun _ => β) → Prop}, P t → (∀ t'' a b h, P t'' → P (t''.insert a b h).impl) → P t' }

/-- Iterate over `l` and insert all of its elements into `t`. -/
@[inline]
def insertMany [Ord α] {ρ : Type w} [ForIn Id ρ (α × β)] (t : Impl α (fun _ => β)) (l : ρ) (h : t.Balanced) :
    IteratedInsertionInto t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for ⟨a, b⟩ in l do
    let hr := r.2 h (fun t'' a b h _ => (t''.insert a b h).balanced_impl)
    r := ⟨r.val.insert a b hr |>.impl, fun h₀ h₁ => h₁ _ _ _ _ (r.2 h₀ h₁)⟩
  return r

/-- A tree map obtained by inserting elements into `t`, bundled with an inductive principle. -/
abbrev IteratedSlowInsertionInto [Ord α] (t) :=
  { t' // ∀ {P : Impl α (fun _ => β) → Prop}, P t → (∀ t'' a b, P t'' → P (t''.insert! a b)) → P t' }

/--
Slower version of `insertMany` which can be used in absence of balance information but still
assumes the preconditions of `insertMany`, otherwise might panic.
-/
@[inline]
def insertMany! [Ord α] {ρ : Type w} [ForIn Id ρ (α × β)] (t : Impl α (fun _ => β)) (l : ρ) :
    IteratedSlowInsertionInto t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for ⟨a, b⟩ in l do
    r := ⟨r.val.insert! a b, fun h₀ h₁ => h₁ _ _ _ (r.2 h₀ h₁)⟩
  return r

/-- A tree map obtained by inserting elements into `t`, bundled with an inductive principle. -/
abbrev IteratedUnitInsertionInto [Ord α] (t) :=
  { t' // ∀ {P : Impl α (fun _ => Unit) → Prop}, P t →
    (∀ t'' a h, P t'' → P (t''.insertIfNew a () h).impl) → P t' }

/-- Iterate over `l` and insert all of its elements into `t`. -/
@[inline]
def insertManyIfNewUnit [Ord α] {ρ : Type w} [ForIn Id ρ α] (t : Impl α (fun _ => Unit)) (l : ρ) (h : t.Balanced) :
    IteratedUnitInsertionInto t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for a in l do
    let hr := r.2 h (fun t'' a h _ => (t''.insertIfNew a () h).balanced_impl)
    r := ⟨r.val.insertIfNew a () hr |>.impl, fun h₀ h₁ => h₁ _ _ _ (r.2 h₀ h₁)⟩
  return r

/-- A tree map obtained by inserting elements into `t`, bundled with an inductive principle. -/
abbrev IteratedSlowUnitInsertionInto [Ord α] (t) :=
  { t' // ∀ {P : Impl α (fun _ => Unit) → Prop}, P t →
    (∀ t'' a, P t'' → P (t''.insertIfNew! a ())) → P t' }

/--
Slower version of `insertManyIfNewUnit` which can be used in absence of balance information but still
assumes the preconditions of `insertManyIfNewUnit`, otherwise might panic.
-/
@[inline]
def insertManyIfNewUnit! [Ord α] {ρ : Type w} [ForIn Id ρ α] (t : Impl α (fun _ => Unit)) (l : ρ) :
    IteratedSlowUnitInsertionInto t := Id.run do
  let mut r := ⟨t, fun h _ => h⟩
  for a in l do
    r := ⟨r.val.insertIfNew! a (), fun h₀ h₁ => h₁ _ _ (r.2 h₀ h₁)⟩
  return r

end Const

variable (α β) in
/-- A balanced tree. -/
structure BalancedTree where
  /-- The tree. -/
  impl : Impl α β
  /-- The tree is balanced. -/
  balanced_impl : impl.Balanced

attribute [Std.Internal.tree_tac] BalancedTree.balanced_impl

/-- Transforms an element of `SizedBalancedTree` into a `BalancedTree`. -/
def SizedBalancedTree.toBalancedTree {lb ub} (t : SizedBalancedTree α β lb ub) : BalancedTree α β :=
  ⟨t.impl, t.balanced_impl⟩

/-- Transforms an array of mappings into a tree map. -/
@[inline]
def ofArray [Ord α] (a : Array ((a : α) × β a)) : Impl α β :=
  empty.insertMany a balanced_empty |>.val

/-- Transforms a list of mappings into a tree map. -/
@[inline]
def ofList [Ord α] (l : List ((a : α) × β a)) : Impl α β :=
  empty.insertMany l balanced_empty |>.val

namespace Const

variable {β : Type v}

/-- Implementation detail of the tree map -/
@[inline]
def getThenInsertIfNew? [Ord α] (t : Impl α (fun _ => β)) (k : α) (v : β)
    (ht : t.Balanced) : Option β × Impl α (fun _ => β) :=
  match get? t k with
  | none => (none, t.insertIfNew k v ht |>.impl)
  | some b => (some b, t)

/--
Slower version of `getThenInsertIfNew?` which can be used in the absence of balance
information but still assumes the preconditions of `getThenInsertIfNew?`, otherwise might panic.
-/
@[inline]
def getThenInsertIfNew?! [Ord α] (t : Impl α (fun _ => β)) (k : α) (v : β)
    : Option β × Impl α (fun _ => β) :=
  match get? t k with
  | none => (none, t.insertIfNew! k v)
  | some b => (some b, t)

/-- Transforms a list of mappings into a tree map. -/
@[inline] def ofArray [Ord α] (a : Array (α × β)) :  Impl α (fun _ => β) :=
  insertMany empty a balanced_empty |>.val

/-- Transforms an array of mappings into a tree map. -/
@[inline] def ofList [Ord α] (l : List (α × β)) : Impl α (fun _ => β) :=
  insertMany empty l balanced_empty |>.val

/-- Transforms a list of mappings into a tree map. -/
@[inline] def unitOfArray [Ord α] (a : Array α) :  Impl α (fun _ => Unit) :=
  insertManyIfNewUnit empty a balanced_empty |>.val

/-- Transforms an array of mappings into a tree map. -/
@[inline] def unitOfList [Ord α] (l : List α) : Impl α (fun _ => Unit) :=
  insertManyIfNewUnit empty l balanced_empty |>.val

end Const

/--
Returns the tree consisting of the mappings `(k, (f k v).get)` where `(k, v)` was a mapping in
the original tree and `(f k v).isSome`.
-/
@[specialize]
def filterMap [Ord α] (f : (a : α) → β a → Option (γ a)) (t : Impl α β) (hl : t.Balanced) :
    BalancedTree α γ :=
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

/--
Slower version of `filterMap` which can be used in the absence of balance
information but still assumes the preconditions of `filterMap`, otherwise might panic.
-/
@[specialize]
def filterMap! [Ord α] (f : (a : α) → β a → Option (γ a)) (t : Impl α β) : Impl α γ :=
  match t with
  | .leaf => .leaf
  | .inner _ k v l r =>
    match f k v with
    | none => link2! (filterMap! f l) (filterMap! f r)
    | some v' => link! k v' (filterMap! f l) (filterMap! f r)

/--
Returns the tree consisting of the mappings `(k, f k v)` where `(k, v)` was a mapping in the
original tree.
-/
@[specialize]
def map [Ord α] (f : (a : α) → β a → γ a) (t : Impl α β) : Impl α γ :=
  match t with
  | .leaf => .leaf
  | .inner sz k v l r => .inner sz k (f k v) (map f l) (map f r)

/--
Monadic version of `map`.
-/
@[specialize]
def mapM {α : Type v} {β γ : α → Type v} {M : Type v → Type v} [Applicative M]
    (f : (a : α) → β a → M (γ a)) : Impl α β → M (Impl α γ)
  | leaf => pure leaf
  | inner sz k v l r => pure (.inner sz k) <*> f k v <*> l.mapM f <*> r.mapM f

/--
Returns the tree consisting of the mapping `(k, v)` where `(k, v)` was a mapping in the
original tree and `f k v = true`.
-/
@[specialize]
def filter [Ord α] (f : (a : α) → β a → Bool) (t : Impl α β) (hl : Balanced t) : BalancedTree α β :=
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

/--
Slower version of `filter` which can be used in the absence of balance
information but still assumes the preconditions of `filter`, otherwise might panic.
-/
@[specialize]
def filter! [Ord α] (f : (a : α) → β a → Bool) (t : Impl α β) : Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner _ k v l r =>
    match f k v with
    | false => link2! (filter! f l) (filter! f r)
    | true => link! k v (filter! f l) (filter! f r)

/--
Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it.
This version of the function requires `LawfulEqOrd α`. There is an alternative non-dependent version
called `Const.alter`.
-/
@[specialize]
def alter [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (t : Impl α β)
    (hl : t.Balanced) : SizedBalancedTree α β (t.size - 1) (t.size + 1) :=
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
      match f (some (cast (congrArg β <| compare_eq_iff_eq.mp h).symm v')) with
      | none => ⟨glue l' r' ✓ ✓ ✓, ✓, ✓, ✓⟩
      | some v => ⟨.inner sz k v l' r', ✓, ✓, ✓⟩

/--
Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic.
-/
@[specialize]
def alter! [Ord α] [LawfulEqOrd α] (k : α) (f : Option (β k) → Option (β k)) (t : Impl α β) :
    Impl α β :=
  match t with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match h : compare k k' with
    | .lt => balance! k' v' (alter! k f l') r'
    | .gt => balance! k' v' l' (alter! k f r')
    | .eq =>
      match f (some (cast (congrArg β <| compare_eq_iff_eq.mp h).symm v')) with
      | none => glue! l' r'
      | some v => .inner sz k v l' r'

/-- Internal implementation detail of the tree map -/
@[specialize]
def modify [Ord α] [LawfulEqOrd α] (k : α) (f : β k → β k) (t : Impl α β) :
    Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k' v' l r =>
    match h : compare k k' with
    | .lt => .inner sz k' v' (modify k f l) r
    | .gt => .inner sz k' v' l (modify k f r)
    | .eq => .inner sz k (f <| cast (congrArg β <| compare_eq_iff_eq.mp h).symm v') l r

@[Std.Internal.tree_tac]
theorem aux_size_modify [Ord α] [LawfulEqOrd α] {k f} {t : Impl α β} :
    (t.modify k f).size = t.size := by
  unfold modify
  split <;> (try split) <;> rfl

theorem balanced_modify [Ord α] [LawfulEqOrd α] {k f} {t : Impl α β} (ht : t.Balanced) :
    (t.modify k f).Balanced := by
  induction t with
  | leaf => exact balanced_empty
  | inner sz k v l r ihl ihr =>
    dsimp only  [modify]
    have ihl := ihl ht.left
    have ihr := ihr ht.right
    tree_tac

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.
-/
@[inline]
def mergeWith [Ord α] [LawfulEqOrd α] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Impl α β)
    (ht₁ : t₁.Balanced) : BalancedTree α β :=
  t₂.foldl (δ := BalancedTree α β) (init := (⟨t₁, ht₁⟩ : BalancedTree α β)) fun t a b₂ =>
    (t.impl.alter a (fun
      | none => some b₂
      | some b₁ => some <| mergeFn a b₁ b₂) t.balanced_impl).toBalancedTree

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.
-/
@[inline]
def mergeWith! [Ord α] [LawfulEqOrd α] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Impl α β) :
    Impl α β :=
  t₂.foldl (init := t₁) fun t a b₂ =>
    t.alter! a fun
      | none => some b₂
      | some b₁ => some <| mergeFn a b₁ b₂

namespace Const

variable {β : Type v}
local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

/--
Changes the mapping of the key `k` by applying the function `f` to the current mapped value
(if any). This function can be used to insert a new mapping, modify an existing one or delete it.
This version of the function requires `LawfulEqOrd α`. There is an alternative non-dependent version
called `Const.alter`.
-/
@[specialize]
def alter [Ord α] (k : α) (f : Option β → Option β) (t : Impl α β)
    (hl : t.Balanced) : SizedBalancedTree α β (t.size - 1) (t.size + 1) :=
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
      | some v => ⟨.inner sz k v l' r', ✓, ✓, ✓⟩

/--
Slower version of `modify` which can be used in the absence of balance
information but still assumes the preconditions of `modify`, otherwise might panic.
-/
@[specialize]
def alter! [Ord α] (k : α) (f : Option β → Option β) (t : Impl α β) :
    Impl α β :=
  match t with
  | .leaf =>
    match f none with
    | none => .leaf
    | some v => .inner 1 k v .leaf .leaf
  | .inner sz k' v' l' r' =>
    match compare k k' with
    | .lt => balance! k' v' (alter! k f l') r'
    | .gt => balance! k' v' l' (alter! k f r')
    | .eq =>
      match f (some v') with
      | none => glue! l' r'
      | some v => .inner sz k v l' r'

/-- Internal implementation detail of the tree map -/
@[specialize]
def modify [Ord α] (k : α) (f : β → β) (t : Impl α β) :
    Impl α β :=
  match t with
  | .leaf => .leaf
  | .inner sz k' v' l r =>
    match compare k k' with
    | .lt => .inner sz k' v' (modify k f l) r
    | .gt => .inner sz k' v' l (modify k f r)
    | .eq => .inner sz k (f v') l r

@[Std.Internal.tree_tac]
theorem aux_size_modify [Ord α] {k f} {t : Impl α β} :
    (modify k f t).size = t.size := by
  unfold modify
  split <;> (try split) <;> rfl

theorem balanced_modify [Ord α] {k f} {t : Impl α β} (ht : t.Balanced) :
    (modify k f t).Balanced := by
  induction t with
  | leaf => exact balanced_empty
  | inner sz k v l r ihl ihr =>
    dsimp only  [modify]
    have ihl := ihl ht.left
    have ihr := ihr ht.right
    exact ✓

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.
-/
@[inline]
def mergeWith [Ord α] (mergeFn : (a : α) → β → β → β) (t₁ t₂ : Impl α β)
    (ht₁   : t₁.Balanced) : BalancedTree α β :=
  t₂.foldl (δ := BalancedTree α β) (init := (⟨t₁, ht₁⟩ : BalancedTree α β)) fun t a b₂ =>
    (alter a (fun
      | none => some b₂
      | some b₁ => some <| mergeFn a b₁ b₂) t.impl t.balanced_impl).toBalancedTree

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.
-/
@[inline]
def mergeWith! [Ord α] (mergeFn : (a : α) → β → β → β) (t₁ t₂ : Impl α β) : Impl α β :=
  t₂.foldl (init := t₁) fun t a b₂ =>
    alter! (t := t) a fun
      | none => some b₂
      | some b₁ => some <| mergeFn a b₁ b₂

end Const

end Std.DTreeMap.Internal.Impl
