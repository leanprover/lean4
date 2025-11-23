/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Std.Data.DTreeMap.Internal.Lemmas
public import Std.Data.DTreeMap.Raw.AdditionalOperations

@[expose] public section

/-!
# Well-formedness proofs for raw dependent tree maps

This file contains well-formedness proofs about `Std.Data.DTreeMap.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v

namespace Std.DTreeMap.Raw.WF

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering} {t : Raw α β cmp}
local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

theorem empty : (empty : Raw α β cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.empty⟩

theorem emptyc : (∅ : Raw α β cmp).WF :=
  empty

theorem erase [TransCmp cmp] {a} (h : t.WF) : WF (t.erase a) :=
  ⟨h.out.erase!⟩

theorem insert [TransCmp cmp] {a b} (h : t.WF) : WF (t.insert a b) :=
  ⟨h.out.insert!⟩

theorem insertIfNew [TransCmp cmp] {a b} (h : t.WF) : WF (t.insertIfNew a b) :=
  ⟨h.out.insertIfNew!⟩

theorem containsThenInsert [TransCmp cmp] {a b} (h : t.WF) : WF (t.containsThenInsert a b).2 :=
  ⟨h.out.containsThenInsert!⟩

theorem containsThenInsertIfNew [TransCmp cmp] {a b} (h : t.WF) : WF (t.containsThenInsertIfNew a b).2 :=
  ⟨h.out.containsThenInsertIfNew!⟩

theorem getThenInsertIfNew? [TransCmp cmp] [LawfulEqCmp cmp] {a b} (h : t.WF) :
    WF (t.getThenInsertIfNew? a b).2 :=
  ⟨h.out.getThenInsertIfNew?!⟩

theorem filter [TransCmp cmp] {f} (h : t.WF) :
    WF (t.filter f) :=
  ⟨h.out.filter!⟩

theorem filterMap [TransCmp cmp] {f : (a : α) → β a → Option (β a)} (h : t.WF) :
    WF (t.filterMap f) :=
  ⟨h.out.filterMap!⟩

theorem partition_fst [TransCmp cmp] {f} :
    WF (t.partition f).fst := by
  rw [partition, foldl, Impl.foldl_eq_foldl, ← List.foldr_reverse]
  induction t.inner.toListModel.reverse  with
  | nil => exact empty
  | cons e es ih =>
    simp only [List.foldr_cons]
    split
    · exact ih.insert
    · exact ih

theorem partition_snd [TransCmp cmp] {f} :
    WF (t.partition f).snd := by
  rw [partition, foldl, Impl.foldl_eq_foldl, ← List.foldr_reverse]
  induction t.inner.toListModel.reverse  with
  | nil => exact empty
  | cons e es ih =>
    simp only [List.foldr_cons]
    split
    · exact ih
    · exact ih.insert

theorem eraseMany [TransCmp cmp] {ρ} [ForIn Id ρ α] [ForInNew Id ρ α] {l : ρ} {t : Raw α β cmp}
    (h : t.WF) : WF (t.eraseMany l) :=
  ⟨h.out.eraseMany!⟩

theorem insertMany [TransCmp cmp] {ρ} [ForIn Id ρ ((a : α) × β a)] [ForInNew Id ρ ((a : α) × β a)] {l : ρ} {t : Raw α β cmp}
    (h : t.WF) : WF (t.insertMany l) :=
  ⟨h.out.insertMany!⟩

theorem ofList [TransCmp cmp] {l : List ((a : α) × β a)} :
    (Raw.ofList l cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.insertMany Impl.WF.empty⟩

theorem ofArray [TransCmp cmp] {a : Array ((a : α) × β a)} :
    (Raw.ofArray a cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.insertMany Impl.WF.empty⟩

theorem alter [LawfulEqCmp cmp] {a f} {t : Raw α β cmp} (h : t.WF) :
    (t.alter a f).WF :=
  ⟨h.out.alter! (t := t.inner) (a := a) (f := f)⟩

theorem modify [LawfulEqCmp cmp] {a f} {t : Raw α β cmp} (h : t.WF) :
    (t.modify a f).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨h.out.modify⟩

theorem mergeWith [LawfulEqCmp cmp] {mergeFn} {t₁ t₂ : Raw α β cmp} (h : t₁.WF) :
    (t₁.mergeWith mergeFn t₂).WF :=
  ⟨h.out.mergeWith!⟩

section Const

variable {β : Type v} {t : Raw α β cmp}

theorem constGetThenInsertIfNew? [TransCmp cmp] {a b} (h : t.WF) :
    WF (Raw.Const.getThenInsertIfNew? t a b).2 :=
  ⟨h.out.constGetThenInsertIfNew?!⟩

theorem constInsertMany [TransCmp cmp] {ρ} [ForIn Id ρ (α × β)] [ForInNew Id ρ (α × β)] {l : ρ} {t : Raw α β cmp}
    (h : t.WF) : WF (Const.insertMany t l) :=
  ⟨h.out.constInsertMany!⟩

theorem constInsertManyIfNewUnit [TransCmp cmp] {ρ} [ForIn Id ρ α] [ForInNew Id ρ α] {l : ρ} {t : Raw α Unit cmp}
    (h : t.WF) : WF (Const.insertManyIfNewUnit t l) :=
  ⟨h.out.constInsertManyIfNewUnit!⟩

theorem constOfList [TransCmp cmp] {l : List (α × β)} :
    (Raw.Const.ofList l cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.constInsertMany Impl.WF.empty⟩

theorem constOfArray [TransCmp cmp] {a : Array (α × β)} :
    (Raw.Const.ofArray a cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.constInsertMany Impl.WF.empty⟩

theorem unitOfList [TransCmp cmp] {l : List α} :
    (Raw.Const.unitOfList l cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.constInsertManyIfNewUnit Impl.WF.empty⟩

theorem unitOfArray [TransCmp cmp] {a : Array α} :
    (Raw.Const.unitOfArray a cmp).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.WF.constInsertManyIfNewUnit Impl.WF.empty⟩

theorem constAlter {a f} {t : Raw α β cmp} (h : t.WF) :
    (Const.alter t a f).WF :=
  ⟨h.out.constAlter!⟩

theorem constModify {a f} {t : Raw α β cmp} (h : t.WF) :
    (Const.modify t a f).WF :=
  letI : Ord α := ⟨cmp⟩; ⟨h.out.constModify⟩

theorem constMergeWith {mergeFn} {t₁ t₂ : Raw α β cmp} (h : t₁.WF) :
    (Const.mergeWith mergeFn t₁ t₂).WF :=
  ⟨h.out.constMergeWith!⟩

theorem union [TransCmp cmp] {t₁ t₂ : Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF):
    (t₁ ∪ t₂).WF :=
  ⟨Impl.WF.union! h₁.out h₂.out⟩

theorem inter [TransCmp cmp] {t₁ t₂ : Raw α β cmp} (h₁ : t₁.WF) :
    (t₁ ∩ t₂).WF :=
  ⟨Impl.WF.inter! h₁.out⟩

theorem diff [TransCmp cmp] {t₁ t₂ : Raw α β cmp} (h₁ : t₁.WF) :
    (t₁ \ t₂).WF :=
  ⟨Impl.WF.diff! h₁.out⟩

end Std.DTreeMap.Raw.WF.Const
