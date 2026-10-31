/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Data.DTreeMap.Basic
public import Std.Data.DTreeMap.Internal.Fold
import Std.Data.DTreeMap.Lemmas

@[expose] public section

/-! Joint ordered folds over two maps. -/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w x

namespace Std.DTreeMap

open Std.DTreeMap.Internal

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type x}
  {cmp : α → α → Ordering}

/--
Folds over the union of two maps in increasing comparator order. The callback receives
`some` on exactly the sides containing the key, and is never called with two `none` values.
A shared key is passed using the representative stored in the first map.

The traversal takes `O(m + n)` time and `O(log m + log n)` additional space for balanced trees.
It uses two traversal stacks without materializing lists of entries.
-/
@[inline]
def foldl₂ [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    (left : DTreeMap α β cmp) (right : DTreeMap α γ cmp) : δ :=
  letI : Ord α := ⟨cmp⟩
  Impl.foldl₂ (fun acc a av => f acc a (some av) none)
    (fun acc a av _ bv h => f acc a (some av)
      (some (cast (congrArg γ (LawfulEqCmp.eq_of_compare h).symm) bv)))
    (fun acc b bv => f acc b none (some bv)) init left.inner right.inner

/-- Ordered list specification for `foldl₂`. -/
theorem foldl₂_eq_foldl₂List [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    (left : DTreeMap α β cmp) (right : DTreeMap α γ cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      foldl₂List (fun acc a av => f acc a (some av) none)
    (fun acc a av _ bv h => f acc a (some av)
      (some (cast (congrArg γ (LawfulEqCmp.eq_of_compare h).symm) bv)))
    (fun acc b bv => f acc b none (some bv)) init left.toList right.toList := by
  letI : Ord α := ⟨cmp⟩
  exact Impl.foldl₂_eq _ _ _ _ _ _

theorem Equiv.foldl₂ [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    {left₁ left₂ : DTreeMap α β cmp} {right₁ right₂ : DTreeMap α γ cmp}
    (hl : left₁ ~m left₂) (hr : right₁ ~m right₂) :
    foldl₂ f init left₁ right₁ = foldl₂ f init left₂ right₂ := by
  letI : Ord α := ⟨cmp⟩
  rw [foldl₂_eq_foldl₂List, foldl₂_eq_foldl₂List, equiv_iff_toList_eq.mp hl,
    equiv_iff_toList_eq.mp hr]

@[simp]
theorem foldl₂_empty_left [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    (right : DTreeMap α γ cmp) :
    foldl₂ f init ∅ right = right.foldl (fun acc k v => f acc k none (some v)) init := by
  letI : Ord α := ⟨cmp⟩
  rw [foldl₂_eq_foldl₂List, DTreeMap.foldl_eq_foldl_toList]
  exact foldl₂List_nil_left _ _ _ _ _

@[simp]
theorem foldl₂_empty_right [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    (left : DTreeMap α β cmp) :
    foldl₂ f init left ∅ = left.foldl (fun acc k v => f acc k (some v) none) init := by
  letI : Ord α := ⟨cmp⟩
  rw [foldl₂_eq_foldl₂List, DTreeMap.foldl_eq_foldl_toList]
  exact foldl₂List_nil_right _ _ _ _ _

namespace Const

variable {β : Type v} {γ : Type w}

@[inline, inherit_doc DTreeMap.foldl₂]
def foldl₂
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : DTreeMap α (fun _ => β) cmp) (right : DTreeMap α (fun _ => γ) cmp) : δ :=
  letI : Ord α := ⟨cmp⟩
  Impl.foldl₂ (fun acc a av => f acc a (some av) none)
    (fun acc a av _ bv _ => f acc a (some av) (some bv))
    (fun acc b bv => f acc b none (some bv)) init left.inner right.inner

/-- Ordered list specification for `foldl₂`. -/
theorem foldl₂_eq
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : DTreeMap α (fun _ => β) cmp) (right : DTreeMap α (fun _ => γ) cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      foldl₂List (fun acc a av => f acc a (some av) none)
    (fun acc a av _ bv _ => f acc a (some av) (some bv))
    (fun acc b bv => f acc b none (some bv)) init (DTreeMap.toList left) (DTreeMap.toList right) := by
  letI : Ord α := ⟨cmp⟩
  exact Impl.foldl₂_eq _ _ _ _ _ _

@[simp]
theorem foldl₂_empty_left
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (right : DTreeMap α (fun _ => γ) cmp) :
    foldl₂ f init ∅ right = right.foldl (fun acc k v => f acc k none (some v)) init := by
  letI : Ord α := ⟨cmp⟩
  rw [foldl₂_eq, DTreeMap.foldl_eq_foldl_toList]
  exact foldl₂List_nil_left _ _ _ _ _

@[simp]
theorem foldl₂_empty_right
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : DTreeMap α (fun _ => β) cmp) :
    foldl₂ f init left ∅ = left.foldl (fun acc k v => f acc k (some v) none) init := by
  letI : Ord α := ⟨cmp⟩
  rw [foldl₂_eq, DTreeMap.foldl_eq_foldl_toList]
  exact foldl₂List_nil_right _ _ _ _ _

/-- Ordered list specification for the nondependent joint fold. -/
theorem foldl₂_eq_foldl₂List (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : DTreeMap α (fun _ => β) cmp) (right : DTreeMap α (fun _ => γ) cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      Internal.Const.foldl₂List f init (toList left) (toList right) := by
  letI : Ord α := ⟨cmp⟩
  simp only [foldl₂, Internal.Const.foldl₂List, DTreeMap.Const.toList,
    Impl.Const.toList_toSigma, Impl.foldl₂_eq]

end Const

theorem Equiv.constFoldl₂ [TransCmp cmp] {β : Type v} {γ : Type w}
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    {left₁ left₂ : DTreeMap α (fun _ => β) cmp} {right₁ right₂ : DTreeMap α (fun _ => γ) cmp}
    (hl : left₁ ~m left₂) (hr : right₁ ~m right₂) :
    Const.foldl₂ f init left₁ right₁ = Const.foldl₂ f init left₂ right₂ := by
  rw [Const.foldl₂_eq, Const.foldl₂_eq, equiv_iff_toList_eq.mp hl,
    equiv_iff_toList_eq.mp hr]

end Std.DTreeMap
