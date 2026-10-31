/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Data.ExtDTreeMap.Basic
public import Std.Data.DTreeMap.Fold

@[expose] public section

/-! Joint ordered folds over two maps. -/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w x

namespace Std.ExtDTreeMap

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type x}
  {cmp : α → α → Ordering}

@[inline, inherit_doc DTreeMap.foldl₂]
def foldl₂ [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    (left : ExtDTreeMap α β cmp) (right : ExtDTreeMap α γ cmp) : δ :=
  Quotient.liftOn₂ left.inner right.inner (fun l r => DTreeMap.foldl₂ f init l r)
    (fun _ _ _ _ hl hr => DTreeMap.Equiv.foldl₂ f init hl hr)


@[simp]
theorem foldl₂_empty_left [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ) (right : ExtDTreeMap α γ cmp) :
    foldl₂ f init ∅ right = foldl (fun acc k v => f acc k none (some v)) init right :=
  right.inductionOn (fun _ => DTreeMap.foldl₂_empty_left f init _)

@[simp]
theorem foldl₂_empty_right [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ) (left : ExtDTreeMap α β cmp) :
    foldl₂ f init left ∅ = foldl (fun acc k v => f acc k (some v) none) init left :=
  left.inductionOn (fun _ => DTreeMap.foldl₂_empty_right f init _)

/-- Ordered list specification for `foldl₂`. -/
theorem foldl₂_eq_foldl₂List [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → (a : α) → Option (β a) → Option (γ a) → δ) (init : δ)
    (left : ExtDTreeMap α β cmp) (right : ExtDTreeMap α γ cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      DTreeMap.Internal.foldl₂List (fun acc a av => f acc a (some av) none)
    (fun acc a av _ bv h => f acc a (some av)
      (some (cast (congrArg γ (LawfulEqCmp.eq_of_compare h).symm) bv)))
    (fun acc b bv => f acc b none (some bv)) init left.toList right.toList :=
  left.inductionOn (fun _ => right.inductionOn (fun _ => DTreeMap.foldl₂_eq_foldl₂List f init _ _))

namespace Const

variable {β : Type v} {γ : Type w}

@[inline, inherit_doc DTreeMap.foldl₂]
def foldl₂ [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : ExtDTreeMap α (fun _ => β) cmp) (right : ExtDTreeMap α (fun _ => γ) cmp) : δ :=
  Quotient.liftOn₂ left.inner right.inner (fun l r => DTreeMap.Const.foldl₂ f init l r)
    (fun _ _ _ _ hl hr => DTreeMap.Equiv.constFoldl₂ f init hl hr)


@[simp]
theorem foldl₂_empty_left [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ) (right : ExtDTreeMap α (fun _ => γ) cmp) :
    foldl₂ f init ∅ right = ExtDTreeMap.foldl (fun acc k v => f acc k none (some v)) init right :=
  right.inductionOn (fun _ => DTreeMap.Const.foldl₂_empty_left f init _)

@[simp]
theorem foldl₂_empty_right [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ) (left : ExtDTreeMap α (fun _ => β) cmp) :
    foldl₂ f init left ∅ = ExtDTreeMap.foldl (fun acc k v => f acc k (some v) none) init left :=
  left.inductionOn (fun _ => DTreeMap.Const.foldl₂_empty_right f init _)

/-- Ordered list specification for the nondependent joint fold. -/
theorem foldl₂_eq_foldl₂List [TransCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : ExtDTreeMap α (fun _ => β) cmp) (right : ExtDTreeMap α (fun _ => γ) cmp) :
    foldl₂ f init left right =
      letI : Ord α := ⟨cmp⟩
      DTreeMap.Internal.Const.foldl₂List f init (toList left) (toList right) :=
  left.inductionOn (fun _ => right.inductionOn (fun _ => DTreeMap.Const.foldl₂_eq_foldl₂List f init _ _))

end Const

end Std.ExtDTreeMap
