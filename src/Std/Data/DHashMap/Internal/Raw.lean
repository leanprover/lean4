/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Basic

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: relating operations on `Raw` to operations on `Raw₀`
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

namespace Std.DHashMap.Internal

namespace Raw

theorem empty_eq [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β) = (Raw₀.empty c).1 := rfl

theorem emptyc_eq [BEq α] [Hashable α] : (∅ : Raw α β) = Raw₀.empty.1 := rfl

theorem insert_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    m.insert a b = (Raw₀.insert ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.insert, h.size_buckets_pos]

theorem insertIfNew_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    m.insertIfNew a b = (Raw₀.insertIfNew ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.insertIfNew, h.size_buckets_pos]

theorem containsThenInsert_snd_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.containsThenInsert a b).2 = (Raw₀.containsThenInsert ⟨m, h.size_buckets_pos⟩ a b).2.1 := by
  simp [Raw.containsThenInsert, h.size_buckets_pos]

theorem containsThenInsert_fst_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} {b : β a} :
    (m.containsThenInsert a b).1 = (Raw₀.containsThenInsert ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.containsThenInsert, h.size_buckets_pos]

theorem containsThenInsertIfNew_snd_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α}
    {b : β a} : (m.containsThenInsertIfNew a b).2 =
      (Raw₀.containsThenInsertIfNew ⟨m, h.size_buckets_pos⟩ a b).2.1 := by
  simp [Raw.containsThenInsertIfNew, h.size_buckets_pos]

theorem containsThenInsertIfNew_fst_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α}
    {b : β a} : (m.containsThenInsertIfNew a b).1 =
      (Raw₀.containsThenInsertIfNew ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.containsThenInsertIfNew, h.size_buckets_pos]

theorem getThenInsertIfNew?_snd_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF)
    {a : α} {b : β a} : (m.getThenInsertIfNew? a b).2 =
      (Raw₀.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).2.1 := by
  simp [Raw.getThenInsertIfNew?, h.size_buckets_pos]

theorem getThenInsertIfNew?_fst_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF)
    {a : α} {b : β a} : (m.getThenInsertIfNew? a b).1 =
      (Raw₀.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.getThenInsertIfNew?, h.size_buckets_pos]

theorem get?_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α} :
    m.get? a = Raw₀.get? ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.get?, h.size_buckets_pos]

theorem contains_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.contains a = Raw₀.contains ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.contains, h.size_buckets_pos]

theorem get_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {a : α} {h : a ∈ m} :
    m.get a h = Raw₀.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
      (by change dite .. = true at h; split at h <;> simp_all) := rfl

theorem getD_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α}
    {fallback : β a} : m.getD a fallback = Raw₀.getD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [Raw.getD, h.size_buckets_pos]

theorem get!_eq [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} (h : m.WF) {a : α}
    [Inhabited (β a)] : m.get! a = Raw₀.get! ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.get!, h.size_buckets_pos]

theorem getKey?_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.getKey? a = Raw₀.getKey? ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.getKey?, h.size_buckets_pos]

theorem getKey_eq [BEq α] [Hashable α] {m : Raw α β} {a : α} {h : a ∈ m} :
    m.getKey a h = Raw₀.getKey ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
      (by change dite .. = true at h; split at h <;> simp_all) := rfl

theorem getKeyD_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a fallback : α} :
    m.getKeyD a fallback = Raw₀.getKeyD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [Raw.getKeyD, h.size_buckets_pos]

theorem getKey!_eq [BEq α] [Hashable α] [Inhabited α] {m : Raw α β} (h : m.WF) {a : α} :
    m.getKey! a = Raw₀.getKey! ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.getKey!, h.size_buckets_pos]

theorem erase_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {a : α} :
    m.erase a = Raw₀.erase ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.erase, h.size_buckets_pos]

theorem filterMap_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF)
    {f : (a : α) → β a → Option (δ a)} : m.filterMap f =
      Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩ := by
  simp [Raw.filterMap, h.size_buckets_pos]

theorem map_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → δ a} :
    m.map f = Raw₀.map f ⟨m, h.size_buckets_pos⟩ := by
  simp [Raw.map, h.size_buckets_pos]

theorem filter_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {f : (a : α) → β a → Bool} :
    m.filter f = Raw₀.filter f ⟨m, h.size_buckets_pos⟩ := by
  simp [Raw.filter, h.size_buckets_pos]

theorem insertMany_eq [BEq α] [Hashable α] {m : Raw α β} (h : m.WF) {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] {l : ρ} :
    m.insertMany l = Raw₀.insertMany ⟨m, h.size_buckets_pos⟩ l := by
  simp [Raw.insertMany, h.size_buckets_pos]

theorem ofList_eq [BEq α] [Hashable α] {l : List ((a : α) × β a)} :
    Raw.ofList l = Raw₀.insertMany Raw₀.empty l := by
  simp only [Raw.ofList, Raw.insertMany, (Raw.WF.empty).size_buckets_pos ∅, ↓reduceDIte]
  congr

theorem alter_eq [BEq α] [LawfulBEq α] [Hashable α] {m : Raw α β} (h : m.WF) {k : α} {f : Option (β k) → Option (β k)} :
    m.alter k f = Raw₀.alter ⟨m, h.size_buckets_pos⟩ k f := by
  simp [Raw.alter, h.size_buckets_pos]

theorem modify_eq [BEq α] [LawfulBEq α] [Hashable α] {m : Raw α β} (h : m.WF) {k : α} {f : β k → β k} :
    m.modify k f = Raw₀.modify ⟨m, h.size_buckets_pos⟩ k f := by
  simp [Raw.modify, h.size_buckets_pos]

section

variable {β : Type v}

theorem Const.insertMany_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {ρ : Type w} [ForIn Id ρ (α × β)] {l : ρ} :
    Raw.Const.insertMany m l = Raw₀.Const.insertMany ⟨m, h.size_buckets_pos⟩ l := by
  simp [Raw.Const.insertMany, h.size_buckets_pos]

theorem Const.ofList_eq [BEq α] [Hashable α] {l : List (α × β)} :
    Raw.Const.ofList l = Raw₀.Const.insertMany Raw₀.empty l := by
  simp only [Raw.Const.ofList, Raw.Const.insertMany, (Raw.WF.empty).size_buckets_pos ∅, ↓reduceDIte]
  congr

theorem Const.insertManyIfNewUnit_eq {ρ : Type w} [ForIn Id ρ α] [BEq α] [Hashable α]
    {m : Raw α (fun _ => Unit)} {l : ρ} (h : m.WF):
    Raw.Const.insertManyIfNewUnit m l = Raw₀.Const.insertManyIfNewUnit ⟨m, h.size_buckets_pos⟩ l := by
  simp [Raw.Const.insertManyIfNewUnit, h.size_buckets_pos]

theorem Const.unitOfList_eq [BEq α] [Hashable α] {l : List α} :
    Raw.Const.unitOfList l = Raw₀.Const.insertManyIfNewUnit Raw₀.empty l := by
  simp only [Raw.Const.unitOfList, Raw.Const.insertManyIfNewUnit, (Raw.WF.empty).size_buckets_pos ∅,
    ↓reduceDIte]
  congr

theorem Const.get?_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α} :
    Raw.Const.get? m a = Raw₀.Const.get? ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.Const.get?, h.size_buckets_pos]

theorem Const.get_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {a : α} {h : a ∈ m} :
    Raw.Const.get m a h = Raw₀.Const.get
      ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
      (by change dite .. = true at h; split at h <;> simp_all) :=
  rfl

theorem Const.getD_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {a : α}
    {fallback : β} : Raw.Const.getD m a fallback =
      Raw₀.Const.getD ⟨m, h.size_buckets_pos⟩ a fallback := by
  simp [Raw.Const.getD, h.size_buckets_pos]

theorem Const.get!_eq [BEq α] [Hashable α] [Inhabited β] {m : Raw α (fun _ => β)} (h : m.WF)
    {a : α} : Raw.Const.get! m a = Raw₀.Const.get! ⟨m, h.size_buckets_pos⟩ a := by
  simp [Raw.Const.get!, h.size_buckets_pos]

theorem Const.getThenInsertIfNew?_snd_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF)
    {a : α} {b : β} : (Raw.Const.getThenInsertIfNew? m a b).2 =
      (Raw₀.Const.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).2.1 := by
  simp [Raw.Const.getThenInsertIfNew?, h.size_buckets_pos]

theorem Const.getThenInsertIfNew?_fst_eq [BEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF)
    {a : α} {b : β} : (Raw.Const.getThenInsertIfNew? m a b).1 =
      (Raw₀.Const.getThenInsertIfNew? ⟨m, h.size_buckets_pos⟩ a b).1 := by
  simp [Raw.Const.getThenInsertIfNew?, h.size_buckets_pos]

theorem Const.alter_eq [BEq α] [EquivBEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {k : α} {f : Option β → Option β} :
    Raw.Const.alter m k f = Raw₀.Const.alter ⟨m, h.size_buckets_pos⟩ k f := by
  simp [Raw.Const.alter, h.size_buckets_pos]

theorem Const.modify_eq [BEq α] [EquivBEq α] [Hashable α] {m : Raw α (fun _ => β)} (h : m.WF) {k : α} {f : β → β} :
    Raw.Const.modify m k f = Raw₀.Const.modify ⟨m, h.size_buckets_pos⟩ k f := by
  simp [Raw.Const.modify, h.size_buckets_pos]

end

end Raw

end Std.DHashMap.Internal
