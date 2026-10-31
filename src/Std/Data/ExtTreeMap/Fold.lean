/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Data.ExtTreeMap.Basic
public import Std.Data.ExtDTreeMap.Fold

@[expose] public section

/-! Joint ordered folds over two maps. -/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w x

namespace Std.ExtTreeMap

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {cmp : α → α → Ordering}

@[inline, inherit_doc DTreeMap.foldl₂]
def foldl₂ [TransCmp cmp] (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : ExtTreeMap α β cmp) (right : ExtTreeMap α γ cmp) : δ :=
  ExtDTreeMap.Const.foldl₂ f init left.inner right.inner


@[simp]
theorem foldl₂_empty_left [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ) (right : ExtTreeMap α γ cmp) :
    foldl₂ f init ∅ right = right.foldl (fun acc k v => f acc k none (some v)) init :=
  ExtDTreeMap.Const.foldl₂_empty_left f init _

@[simp]
theorem foldl₂_empty_right [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ) (left : ExtTreeMap α β cmp) :
    foldl₂ f init left ∅ = left.foldl (fun acc k v => f acc k (some v) none) init :=
  ExtDTreeMap.Const.foldl₂_empty_right f init _

/-- Ordered list specification for the joint fold. -/
theorem foldl₂_eq_foldl₂List [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : ExtTreeMap α β cmp) (right : ExtTreeMap α γ cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      DTreeMap.Internal.Const.foldl₂List f init left.toList right.toList :=
  ExtDTreeMap.Const.foldl₂_eq_foldl₂List f init _ _

end Std.ExtTreeMap
