/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Data.TreeMap.Raw.Basic
public import Std.Data.DTreeMap.Raw.Fold

@[expose] public section

/-! Joint ordered folds over two maps. -/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w x

namespace Std.TreeMap.Raw

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {cmp : α → α → Ordering}

@[inline, inherit_doc DTreeMap.foldl₂]
def foldl₂ (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : Raw α β cmp) (right : Raw α γ cmp) : δ :=
  DTreeMap.Raw.Const.foldl₂ f init left.inner right.inner


@[simp]
theorem foldl₂_empty_left
    (f : δ → α → Option β → Option γ → δ) (init : δ) (right : Raw α γ cmp) :
    foldl₂ f init ∅ right = right.foldl (fun acc k v => f acc k none (some v)) init :=
  DTreeMap.Raw.Const.foldl₂_empty_left f init _

@[simp]
theorem foldl₂_empty_right
    (f : δ → α → Option β → Option γ → δ) (init : δ) (left : Raw α β cmp) :
    foldl₂ f init left ∅ = left.foldl (fun acc k v => f acc k (some v) none) init :=
  DTreeMap.Raw.Const.foldl₂_empty_right f init _

theorem Equiv.foldl₂ [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    {left₁ left₂ : Raw α β cmp} {right₁ right₂ : Raw α γ cmp}
    (hl₁ : left₁.WF) (hl₂ : left₂.WF) (hr₁ : right₁.WF) (hr₂ : right₂.WF)
    (hl : left₁ ~m left₂) (hr : right₁ ~m right₂) :
    foldl₂ f init left₁ right₁ = foldl₂ f init left₂ right₂ :=
  DTreeMap.Raw.Equiv.constFoldl₂ f init hl₁.out hl₂.out hr₁.out hr₂.out hl.inner hr.inner

/-- Ordered list specification for the joint fold. -/
theorem foldl₂_eq_foldl₂List (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : Raw α β cmp) (right : Raw α γ cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      DTreeMap.Internal.Const.foldl₂List f init left.toList right.toList :=
  DTreeMap.Raw.Const.foldl₂_eq_foldl₂List f init _ _

end Std.TreeMap.Raw
