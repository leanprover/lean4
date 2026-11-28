/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Std.Data.DTreeMap.Internal.Zipper
import all Std.Data.DTreeMap.Internal.Zipper
import Init.Omega

@[expose] public section

/-! Joint ordered folds over tree maps, using two traversal stacks. -/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w x

namespace Std.DTreeMap.Internal

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {δ : Type x} [Ord α]

/-- List specification of the joint ordered fold. -/
def foldl₂List
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ) :
    δ → List ((a : α) × β a) → List ((b : α) × γ b) → δ
  | acc, [], [] => acc
  | acc, a :: as, [] => foldl₂List left both right (left acc a.1 a.2) as []
  | acc, [], b :: bs => foldl₂List left both right (right acc b.1 b.2) [] bs
  | acc, a :: as, b :: bs =>
    match h : compare a.1 b.1 with
    | .lt => foldl₂List left both right (left acc a.1 a.2) as (b :: bs)
    | .eq => foldl₂List left both right (both acc a.1 a.2 b.1 b.2 h) as bs
    | .gt => foldl₂List left both right (right acc b.1 b.2) (a :: as) bs
termination_by _ as bs => as.length + bs.length

theorem foldl₂List_nil_left
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ) (acc : δ) (bs : List ((b : α) × γ b)) :
    foldl₂List left both right acc [] bs = bs.foldl (fun acc b => right acc b.1 b.2) acc := by
  induction bs generalizing acc with
  | nil => simp only [foldl₂List, List.foldl_nil]
  | cons b bs ih => simpa only [foldl₂List, List.foldl_cons] using ih (right acc b.1 b.2)

theorem foldl₂List_nil_right
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ) (acc : δ) (as : List ((a : α) × β a)) :
    foldl₂List left both right acc as [] = as.foldl (fun acc a => left acc a.1 a.2) acc := by
  induction as generalizing acc with
  | nil => simp only [foldl₂List, List.foldl_nil]
  | cons a as ih => simpa only [foldl₂List, List.foldl_cons] using ih (left acc a.1 a.2)

/-- Joint fold over traversal stacks. Only the stacks, never entry lists, are allocated. -/
@[specialize]
def Zipper.foldl₂
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ) :
    δ → Zipper α β → Zipper α γ → δ
  | acc, .done, .done => acc
  | acc, .cons a av aTree aNext, .done =>
    Zipper.foldl₂ left both right (left acc a av) (Zipper.prependMap aTree aNext) .done
  | acc, .done, .cons b bv bt bn =>
    Zipper.foldl₂ left both right (right acc b bv) .done (Zipper.prependMap bt bn)
  | acc, l@(.cons a av aTree aNext), r@(.cons b bv bt bn) =>
    match h : compare a b with
    | .lt => Zipper.foldl₂ left both right (left acc a av) (Zipper.prependMap aTree aNext) r
    | .eq => Zipper.foldl₂ left both right (both acc a av b bv h)
        (Zipper.prependMap aTree aNext) (Zipper.prependMap bt bn)
    | .gt => Zipper.foldl₂ left both right (right acc b bv) l (Zipper.prependMap bt bn)
termination_by _ l r => Zipper.size l + Zipper.size r
decreasing_by all_goals simp_all only [Zipper.size, Zipper.size_prependMap]; omega

/-- The stack implementation agrees with the ordered list specification, even for raw trees. -/
theorem Zipper.foldl₂_eq
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ)
    (acc : δ) (l : Zipper α β) (r : Zipper α γ) :
    Zipper.foldl₂ left both right acc l r = foldl₂List left both right acc l.toList r.toList := by
  fun_induction Zipper.foldl₂ <;>
    simp_all [Zipper.toList, foldl₂List, Zipper.toList_prependMap_eq_append]
  all_goals split <;> simp_all

/-- Joint ordered tree traversal using one stack for each tree. -/
@[inline]
def Impl.foldl₂
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ)
    (acc : δ) (l : Impl α β) (r : Impl α γ) : δ :=
  Zipper.foldl₂ left both right acc (Zipper.prependMap l .done) (Zipper.prependMap r .done)

/-- Ordered list specification for the joint tree traversal. -/
theorem Impl.foldl₂_eq
    (left : δ → (a : α) → β a → δ)
    (both : δ → (a : α) → β a → (b : α) → γ b → compare a b = .eq → δ)
    (right : δ → (b : α) → γ b → δ)
    (acc : δ) (l : Impl α β) (r : Impl α γ) :
    Impl.foldl₂ left both right acc l r = foldl₂List left both right acc l.toList r.toList := by
  simp only [Impl.foldl₂, Zipper.foldl₂_eq, Zipper.toList_prependMap_done]

namespace Const

variable {β : Type v} {γ : Type w}

/-- Nondependent ordered list specification, using the left key on collisions. -/
def foldl₂List (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : List (α × β)) (right : List (α × γ)) : δ :=
  Internal.foldl₂List (fun acc a av => f acc a (some av) none)
    (fun acc a av _ bv _ => f acc a (some av) (some bv))
    (fun acc b bv => f acc b none (some bv)) init
    (left.map (fun p => ⟨p.1, p.2⟩)) (right.map (fun p => ⟨p.1, p.2⟩))

end Const

omit [Ord α] in
theorem Impl.Const.toList_toSigma {β : Type v} (t : Impl α (fun _ => β)) :
    (Impl.Const.toList t).map (fun p => (⟨p.1, p.2⟩ : (_ : α) × β)) = t.toList := by
  simp only [Impl.Const.toList_eq_toListModel_map, Impl.toList_eq_toListModel, List.map_map]
  exact List.map_id _

end Std.DTreeMap.Internal
