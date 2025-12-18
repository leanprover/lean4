/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.DTreeMap.Raw.WF
public import Std.Data.TreeMap.Raw.AdditionalOperations

@[expose] public section

/-!
# Well-formedness proofs for raw tree maps

This file contains well-formedness proofs about `Std.Data.TreeMap.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

namespace Std.TreeMap.Raw.WF

open DTreeMap.Raw renaming WF → InnerWF

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : Raw α β cmp}

theorem empty : (empty : Raw α β cmp).WF :=
  ⟨InnerWF.empty⟩

theorem emptyc : (∅ : Raw α β cmp).WF :=
  empty

theorem erase [TransCmp cmp] {a} (h : t.WF) :
    WF (t.erase a) :=
  ⟨InnerWF.erase h⟩

theorem insert [TransCmp cmp] {a b} (h : t.WF) :
    WF (t.insert a b) :=
  ⟨InnerWF.insert h⟩

theorem insertIfNew [TransCmp cmp] {a b} (h : t.WF) :
    WF (t.insertIfNew a b) :=
  ⟨InnerWF.insertIfNew h⟩

theorem containsThenInsert [TransCmp cmp] {a b} (h : t.WF) :
    WF (t.containsThenInsert a b).2 :=
  ⟨InnerWF.containsThenInsert h⟩

theorem containsThenInsertIfNew [TransCmp cmp] {a b} (h : t.WF) :
    WF (t.containsThenInsertIfNew a b).2 :=
  ⟨InnerWF.containsThenInsertIfNew h⟩

theorem getThenInsertIfNew? [TransCmp cmp] {a b} (h : t.WF) :
    WF (t.getThenInsertIfNew? a b).2 :=
  ⟨InnerWF.constGetThenInsertIfNew? h⟩

theorem filter [TransCmp cmp] {f} (h : t.WF) :
    WF (t.filter f) :=
  ⟨InnerWF.filter h⟩

theorem filterMap [TransCmp cmp] {f : α → β → Option β} (h : t.WF) :
    WF (t.filterMap f) :=
  ⟨InnerWF.filterMap h⟩

theorem partition_fst [TransCmp cmp] {f} :
    WF (t.partition f).fst :=
  ⟨InnerWF.partition_fst⟩

theorem partition_snd [TransCmp cmp] {f} :
    WF (t.partition f).snd :=
  ⟨InnerWF.partition_snd⟩

theorem eraseMany [TransCmp cmp] {ρ} [ForIn Id ρ α] {l : ρ} {t : Raw α β cmp} (h : t.WF) :
    WF (t.eraseMany l) :=
  ⟨InnerWF.eraseMany h⟩

theorem insertMany [TransCmp cmp] {ρ} [ForIn Id ρ (α × β)] {l : ρ} {t : Raw α β cmp}
    (h : t.WF) : WF (t.insertMany l) :=
  ⟨InnerWF.constInsertMany h⟩

theorem insertManyIfNewUnit [TransCmp cmp] {ρ} [ForIn Id ρ α] {l : ρ} {t : Raw α Unit cmp}
    (h : t.WF) : WF (t.insertManyIfNewUnit l) :=
  ⟨InnerWF.constInsertManyIfNewUnit h⟩

theorem ofList [TransCmp cmp] {l : List (α × β)} :
    (Raw.ofList l cmp).WF :=
  ⟨InnerWF.constOfList⟩

theorem ofArray [TransCmp cmp] {a : Array (α × β)} :
    (Raw.ofArray a cmp).WF :=
  ⟨InnerWF.constOfArray⟩

theorem alter {a f} {t : Raw α β cmp} (h : t.WF) :
    (t.alter a f).WF :=
  ⟨InnerWF.constAlter h⟩

theorem modify {a f} {t : Raw α β cmp} (h : t.WF) :
    (t.modify a f).WF :=
  ⟨InnerWF.constModify h⟩

theorem unitOfList [TransCmp cmp] {l : List α} :
    (Raw.unitOfList l cmp).WF :=
  ⟨InnerWF.unitOfList⟩

theorem unitOfArray [TransCmp cmp] {a : Array α} :
    (Raw.unitOfArray a cmp).WF :=
  ⟨InnerWF.unitOfArray⟩

theorem mergeWith {mergeFn} {t₁ t₂ : Raw α β cmp} (h : t₁.WF) :
    (t₁.mergeWith mergeFn t₂).WF :=
  ⟨InnerWF.constMergeWith h⟩

theorem union [TransCmp cmp] {t₁ t₂ : Raw α β cmp} (h₁ : t₁.WF) (h₂ : t₂.WF) :
  (t₁ ∪ t₂).WF :=
  ⟨InnerWF.union h₁ h₂⟩

theorem inter [TransCmp cmp] {t₁ t₂ : Raw α β cmp} (h₁ : t₁.WF) :
    (t₁ ∩ t₂).WF :=
  ⟨InnerWF.inter h₁⟩

theorem diff [TransCmp cmp] {t₁ t₂ : Raw α β cmp} (h₁ : t₁.WF) :
    (t₁ \ t₂).WF :=
  ⟨InnerWF.diff h₁⟩

end Std.TreeMap.Raw.WF
