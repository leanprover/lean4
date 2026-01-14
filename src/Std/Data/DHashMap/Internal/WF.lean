/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
import all Std.Data.Internal.List.Associative
import all Std.Data.DHashMap.Raw
import all Std.Data.DHashMap.Internal.Defs
public import Std.Data.DHashMap.Internal.Model
import all Std.Data.DHashMap.Internal.AssocList.Basic
import all Std.Data.DHashMap.RawDef

public section

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

File contents: proof that all hash map operations preserve `WFImp` to show `WF.out : WF → WFImp`
-/

open Std.Internal.List
open Std.Internal

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

open List

namespace Std.DHashMap.Internal

@[simp]
theorem toListModel_replicate_nil {c} :
    toListModel (Array.replicate c (AssocList.nil : AssocList α β)) = [] := by
  suffices ∀ d, (List.replicate d AssocList.nil).flatMap AssocList.toList = [] from this _
  intro d
  induction d <;> simp_all [List.replicate]

@[simp]
theorem computeSize_eq {buckets : Array (AssocList α β)} :
    computeSize buckets = (toListModel buckets).length := by
  rw [computeSize, toListModel, List.flatMap_eq_foldl, Array.foldl_toList]
  suffices ∀ (l : List (AssocList α β)) (l' : List ((a : α) × β a)),
      l.foldl (fun d b => d + b.toList.length) l'.length =
        (l.foldl (fun acc a => acc ++ a.toList) l').length
    by simpa using this buckets.toList []
  intro l l'
  induction l generalizing l'
  · simp
  next l₂ t ih => rw [foldl_cons, ← List.length_append, ih, foldl_cons]

namespace Raw

theorem equiv_iff_toListModel_perm {m₁ m₂ : Raw α β} :
    m₁.Equiv m₂ ↔ toListModel m₁.2 ~ toListModel m₂.2 :=
  ⟨Raw.Equiv.impl, Raw.Equiv.mk⟩

theorem size_eq_length [BEq α] [Hashable α] {m : Raw α β} (h : Raw.WFImp m) :
    m.size = (toListModel m.buckets).length :=
  h.size_eq

theorem isEmpty_eq_isEmpty [BEq α] [Hashable α] {m : Raw α β} (h : Raw.WFImp m) :
    m.isEmpty = (toListModel m.buckets).isEmpty := by
  rw [Raw.isEmpty, Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, size_eq_length h,
    Nat.beq_eq_true_eq]

theorem fold_eq {l : Raw α β} {f : γ → (a : α) → β a → γ} {init : γ} :
    l.fold f init = l.buckets.foldl (fun acc l => l.foldl f acc) init := (rfl)

theorem fold_cons_apply {l : Raw α β} {acc : List γ} (f : (a : α) → β a → γ) :
    l.fold (fun acc k v => f k v :: acc) acc =
      ((toListModel l.buckets).reverse.map (fun p => f p.1 p.2)) ++ acc := by
  rw [fold_eq, ← Array.foldl_toList, toListModel]
  induction l.buckets.toList generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [foldl_cons, ih, AssocList.foldl_apply]
      simp

theorem fold_cons {l : Raw α β} {acc : List ((a : α) × β a)} :
    l.fold (fun acc k v => ⟨k, v⟩ :: acc) acc = (toListModel l.buckets).reverse ++ acc := by
  simp [fold_cons_apply]

theorem fold_cons_key {l : Raw α β} {acc : List α} :
    l.fold (fun acc k _ => k :: acc) acc = List.keys (toListModel l.buckets).reverse ++ acc := by
  rw [fold_cons_apply, keys_eq_map, map_reverse]

theorem foldRev_eq {l : Raw α β} {f : γ → (a : α) → β a → γ} {init : γ} :
    Raw.Internal.foldRev f init l =
      l.buckets.foldr (fun l acc => l.foldr (fun a b g => f g a b) acc) init := by
  simp only [Raw.Internal.foldRev, Raw.Internal.foldRevM, Array.id_run_foldrM, AssocList.foldr]

theorem foldRev_cons_apply {l : Raw α β} {acc : List γ} (f : (a : α) → β a → γ) :
    Raw.Internal.foldRev (fun acc k v => f k v :: acc) acc l =
      ((toListModel l.buckets).map (fun p => f p.1 p.2)) ++ acc := by
  rw [foldRev_eq, ← Array.foldr_toList, toListModel]
  induction l.buckets.toList generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [foldr_cons, ih, AssocList.foldr_apply]
      simp

theorem fold_push_apply {l : Raw α β} {acc : Array γ} (f : (a : α) → β a → γ) :
    Raw.fold (fun acc k v => acc.push (f k v)) acc l =
      acc ++ ((toListModel l.buckets).toArray.map (fun p => f p.1 p.2)) := by
  rw [fold_eq, ← Array.foldl_toList, toListModel]
  induction l.buckets.toList generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [foldl_cons, ih, AssocList.foldl_push_apply]
      simp

theorem foldRev_cons {l : Raw α β} {acc : List ((a : α) × β a)} :
    Raw.Internal.foldRev (fun acc k v => ⟨k, v⟩ :: acc) acc l = toListModel l.buckets ++ acc := by
  simp [foldRev_cons_apply]

theorem foldRev_cons_mk {β : Type v} {l : Raw α (fun _ => β)} {acc : List (α × β)} :
    Raw.Internal.foldRev (fun acc k v => (k, v) :: acc) acc l =
      (toListModel l.buckets).map (fun ⟨k, v⟩ => (k, v)) ++ acc := by
  simp [foldRev_cons_apply]

theorem foldRev_cons_key {l : Raw α β} {acc : List α} :
    Raw.Internal.foldRev (fun acc k _ => k :: acc) acc l =
      List.keys (toListModel l.buckets) ++ acc := by
  rw [foldRev_cons_apply, keys_eq_map]

theorem foldRev_cons_value {β : Type v} {l : Raw α (fun _ => β)} {acc : List β} :
    Raw.Internal.foldRev (fun acc _ v => v :: acc) acc l =
      List.values (toListModel l.buckets) ++ acc := by
  rw [foldRev_cons_apply, values_eq_map]

theorem fold_push {l : Raw α β} {acc : Array ((a : α) × β a)} :
    Raw.fold (fun acc k v => acc.push ⟨k, v⟩) acc l = acc ++ (toListModel l.buckets).toArray := by
  simp [fold_push_apply]

theorem fold_push_mk {β : Type v} {l : Raw α (fun _ => β)} {acc : Array (α × β)} :
    Raw.fold (fun acc k v => acc.push (k, v)) acc l =
      acc ++ ((toListModel l.buckets).map (fun ⟨k, v⟩ => (k, v))).toArray := by
  simp [fold_push_apply]

theorem fold_push_key {l : Raw α β} {acc : Array α} :
    Raw.fold (fun acc k _ => acc.push k) acc l =
      acc ++ (List.keys (toListModel l.buckets)).toArray := by
  simp [fold_push_apply, keys_eq_map]

theorem foldM_eq_foldlM_toListModel {δ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β a → m δ} {init : δ} {b : Raw α β} :
    b.foldM f init = (toListModel b.buckets).foldlM (fun a b => f a b.1 b.2) init := by
  simp only [Raw.foldM, ← Array.foldlM_toList, toListModel]
  induction b.buckets.toList generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [foldlM_cons, ih, flatMap_cons, foldlM_append]
    congr
    induction hd generalizing init with
    | nil => simp [AssocList.foldlM]
    | cons hda hdb tl ih =>
      simp only [AssocList.foldlM, AssocList.toList_cons, foldlM_cons]
      congr
      funext init'
      rw [ih]

theorem fold_induction {δ : Type w}
    {f : δ → (a : α) → β a → δ} {init : δ} {b : Raw α β} {P : δ → Prop}
    (base : P init) (step : ∀ acc a b , P acc → P (f acc a b)) :
    P (b.fold f init) := by
  simp [Raw.fold, Raw.foldM, ← Array.foldlM_toList]
  induction b.buckets.toList generalizing init with
  | nil => simp [base]
  | cons hd tl ih =>
    apply ih
    induction hd generalizing init with
    | nil => simp [AssocList.foldlM, pure, base]
    | cons hda hdb tl ih =>
      simp only [AssocList.foldlM, pure_bind]
      apply ih
      apply step
      exact base

theorem fold_eq_foldl_toListModel {l : Raw α β} {f : γ → (a : α) → β a → γ} {init : γ} :
    l.fold f init = (toListModel l.buckets).foldl (fun a b => f a b.1 b.2) init := by
  simp [Raw.fold, foldM_eq_foldlM_toListModel]

theorem foldRevM_eq_foldrM_toListModel {δ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {f : δ → (a : α) → β a → m δ} {init : δ} {b : Raw α β} :
    Raw.Internal.foldRevM f init b =
      (toListModel b.buckets).foldrM (fun a b => f b a.1 a.2) init := by
  simp only [Raw.Internal.foldRevM, ← Array.foldrM_toList, toListModel]
  induction b.buckets.toList generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [foldrM_cons, ih, flatMap_cons, foldrM_append]
    congr
    funext init'
    induction hd generalizing init' with
    | nil => simp [AssocList.foldrM]
    | cons hda hdb tl ih =>
      simp only [AssocList.foldrM, AssocList.toList_cons, foldrM_cons]
      congr
      rw [ih]

theorem foldRev_eq_foldr_toListModel {l : Raw α β} {f : γ → (a : α) → β a → γ} {init : γ} :
    Raw.Internal.foldRev f init l =
      (toListModel l.buckets).foldr (fun a b => f b a.1 a.2) init := by
  simp [Raw.Internal.foldRev, foldRevM_eq_foldrM_toListModel]

theorem toList_eq_toListModel {m : Raw α β} : m.toList = toListModel m.buckets := by
  simp [Raw.toList, foldRev_cons]

theorem Const.toList_eq_toListModel_map {β : Type v} {m : Raw α (fun _ => β)} :
    Raw.Const.toList m = (toListModel m.buckets).map (fun ⟨k, v⟩ => ⟨k, v⟩) := by
  simp [Raw.Const.toList, foldRev_cons_mk]

theorem toArray_eq_toArray_toListModel {m : Raw α β} : m.toArray = (toListModel m.buckets).toArray := by
  simp [Raw.toArray, fold_push]

theorem Const.toArray_eq_toArray_map_toListModel {β : Type v} {m : Raw α (fun _ => β)} :
    Raw.Const.toArray m = ((toListModel m.buckets).map (fun ⟨k, v⟩ => (k,v))).toArray := by
  simp [Raw.Const.toArray, fold_push_mk]

theorem keys_eq_keys_toListModel {m : Raw α β} :
    m.keys = List.keys (toListModel m.buckets) := by
  simp [Raw.keys, foldRev_cons_key, keys_eq_map]

theorem values_eq_values_toListModel {β : Type v}  {m : Raw α (fun _ => β)} :
    m.values = List.values (toListModel m.buckets) := by
  simp [Raw.values, foldRev_cons_value, values_eq_map]

theorem keysArray_eq_toArray_keys_toListModel {m : Raw α β} :
    m.keysArray = (List.keys (toListModel m.buckets)).toArray := by
  simp [Raw.keysArray, fold_push_key]

theorem forM_eq_forM_toListModel {l: Raw α β} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → m PUnit} :
    l.forM f = (toListModel l.buckets).forM (fun a => f a.1 a.2) := by
  simp only [Raw.forM, Array.forM, ← Array.foldlM_toList, toListModel]
  induction l.buckets.toList with
  | nil => simp
  | cons hd tl ih =>
    simp only [foldlM_cons, flatMap_cons, forM_eq_forM, forM_append]
    congr
    · simp [AssocList.forM]
      induction hd with
      | nil => simp [AssocList.foldlM]
      | cons hda hdb tl ih =>
        simp only [AssocList.foldlM, AssocList.toList_cons, forM_cons]
        congr
        funext x
        rw [ih]
    · funext x
      simp [ih]

theorem forIn_eq_forIn_toListModel {δ : Type w} {l : Raw α β} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ} :
    l.forIn f init = ForIn.forIn (toListModel l.buckets) init (fun a d => f a.1 a.2 d) := by
  rw [Raw.forIn, ← Array.forIn_toList, toListModel]
  induction l.buckets.toList generalizing init with
  | nil => simp
  | cons hd tl ih =>
    induction hd generalizing init with
    | nil => simpa [AssocList.forInStep, AssocList.forInStep.go] using ih
    | cons k v tl' ih' =>
      simp only [AssocList.forInStep, forIn_cons, AssocList.forInStep.go, LawfulMonad.bind_assoc,
        flatMap_cons, AssocList.toList_cons, cons_append]
      congr
      apply funext
      rintro (⟨d⟩|⟨d⟩)
      · simp
      · simpa using ih'

theorem all_eq_all_toListModel {p : (a: α) → β a → Bool} {m : Raw α β} :
    m.all p = (toListModel m.buckets).all (fun x => p x.1 x.2) := by
  simp only [Raw.all, ForIn.forIn, Bool.not_eq_true, bind_pure_comp, map_pure, Id.run_bind]
  rw [forIn_eq_forIn_toListModel, ← toList_eq_toListModel, forIn_eq_forIn']
  induction m.toList with
  | nil => simp only [all_nil, forIn'_nil, Id.run_pure]
  | cons hd tl ih =>
    simp only [forIn'_eq_forIn, List.all_cons]
    by_cases h : p hd.fst hd.snd = false
    · simp [h]
    · simp only [forIn'_eq_forIn] at ih
      simp [h, ih]

end Raw

namespace Raw₀

/-! # Raw₀.empty -/

@[simp]
theorem toListModel_buckets_emptyWithCapacity {c} : toListModel (emptyWithCapacity c : Raw₀ α β).1.buckets = [] :=
  toListModel_replicate_nil

theorem wfImp_emptyWithCapacity [BEq α] [Hashable α] {c} : Raw.WFImp (emptyWithCapacity c : Raw₀ α β).1 where
  buckets_hash_self := by simp [Raw₀.emptyWithCapacity]
  size_eq := by simp [Raw₀.emptyWithCapacity]
  distinct := by simp

theorem isHashSelf_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) (h : IsHashSelf data.1) :
    IsHashSelf (reinsertAux hash data a b).1 := by
  rw [reinsertAux_eq]
  refine h.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

/-! # expandIfNecessary -/

theorem toListModel_reinsertAux [BEq α] [Hashable α] [PartialEquivBEq α]
    (data : {d : Array (AssocList α β) // 0 < d.size}) (a : α) (b : β a) :
    Perm (toListModel (reinsertAux hash data a b).1) (⟨a, b⟩ :: toListModel data.1) := by
  rw [reinsertAux_eq]
  obtain ⟨l, h₁, h₂, -⟩ := exists_bucket_of_update data.1 data.2 a (fun l => l.cons a b)
  exact h₂.trans (Perm.cons _ (Perm.symm h₁))

theorem isHashSelf_foldl_reinsertAux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (l : List ((a : α) × β a)) (target : { d : Array (AssocList α β) // 0 < d.size }) :
    IsHashSelf target.1 →
      IsHashSelf (l.foldl (fun acc p => reinsertAux hash acc p.1 p.2) target).1 := by
  induction l generalizing target
  · simp
  next k v _ ih => exact fun h => ih _ (isHashSelf_reinsertAux _ _ _ h)

theorem toListModel_foldl_reinsertAux [BEq α] [Hashable α] [PartialEquivBEq α]
    (l : List ((a : α) × β a)) (target : { d : Array (AssocList α β) // 0 < d.size }) :
    Perm (toListModel (l.foldl (fun acc p => reinsertAux hash acc p.1 p.2) target).1)
      (l ++ toListModel target.1) := by
  induction l generalizing target
  · simp
  next k v t ih =>
    simp only [foldl_cons, cons_append]
    refine (ih _).trans ?_
    refine ((toListModel_reinsertAux _ _ _).append_left _).trans perm_middle

private theorem expand.go_pos [Hashable α] {i : Nat} {source : Array (AssocList α β)}
    {target : { d : Array (AssocList α β) // 0 < d.size }} (h : i < source.size) :
    expand.go i source target = go (i + 1)
      (source.set i .nil) ((source[i]).foldl (reinsertAux hash) target) := by
  rw [expand.go]
  simp only [h, dite_true]

private theorem expand.go_neg [Hashable α] {i : Nat} {source : Array (AssocList α β)}
    {target : { d : Array (AssocList α β) // 0 < d.size}} (h : ¬i < source.size) :
    expand.go i source target = target := by
  rw [expand.go]
  simp only [h, dite_false]

private theorem expand.go_eq [BEq α] [Hashable α] [PartialEquivBEq α] (source : Array (AssocList α β))
    (target : {d : Array (AssocList α β) // 0 < d.size}) : expand.go 0 source target =
      (toListModel source).foldl (fun acc p => reinsertAux hash acc p.1 p.2) target := by
  suffices ∀ i, expand.go i source target =
    ((source.toList.drop i).flatMap AssocList.toList).foldl
      (fun acc p => reinsertAux hash acc p.1 p.2) target by
    simpa using this 0
  intro i
  induction i, source, target using expand.go.induct
  next i source target _ hi es newSource newTarget ih =>
    simp only [newSource, newTarget, es] at *
    rw [expand.go_pos hi]
    refine ih.trans ?_
    simp only [AssocList.foldl_eq, Array.toList_set]
    rw [List.drop_eq_getElem_cons hi, List.flatMap_cons, List.foldl_append,
      List.drop_set_of_lt (by omega), Array.getElem_toList]
  next i source target hi =>
    rw [expand.go_neg hi, List.drop_eq_nil_of_le, flatMap_nil, foldl_nil]
    rwa [Array.size_eq_length_toList, Nat.not_lt] at hi

theorem isHashSelf_expand [BEq α] [Hashable α] [LawfulHashable α] [EquivBEq α]
    {buckets : {d : Array (AssocList α β) // 0 < d.size}} : IsHashSelf (expand buckets).1 := by
  simpa [expand, expand.go_eq] using isHashSelf_foldl_reinsertAux _ _ (by simp)

theorem toListModel_expand [BEq α] [Hashable α] [PartialEquivBEq α]
    {buckets : {d : Array (AssocList α β) // 0 < d.size}} :
    Perm (toListModel (expand buckets).1) (toListModel buckets.1) := by
  simpa [expand, expand.go_eq] using toListModel_foldl_reinsertAux (toListModel buckets.1)
    ⟨.replicate (buckets.1.size * 2) .nil, by simpa using Nat.mul_pos buckets.2 Nat.two_pos⟩

theorem toListModel_expandIfNecessary [BEq α] [Hashable α] [PartialEquivBEq α] (m : Raw₀ α β) :
    Perm (toListModel (expandIfNecessary m).1.2) (toListModel m.1.2) := by
  rw [expandIfNecessary]
  dsimp
  split
  · exact Perm.refl _
  · dsimp
    exact toListModel_expand

@[simp]
theorem size_expandIfNecessary [BEq α] [Hashable α] {m : Raw₀ α β} :
    (expandIfNecessary m).val.size = m.val.size := by
  rw [expandIfNecessary]
  split <;> rfl

theorem wfImp_expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) : Raw.WFImp (expandIfNecessary m).1 := by
  rw [Raw₀.expandIfNecessary]
  dsimp
  split
  · exact h
  · let ⟨⟨size, buckets⟩, hm⟩ := m
    have := toListModel_expand (buckets := ⟨buckets, hm⟩)
    dsimp at this
    refine ⟨?_, ?_, ?_⟩
    · simpa using isHashSelf_expand
    · refine h.size_eq.trans ?_
      simpa using this.symm.length_eq
    · simpa using h.distinct.perm this

/-! # Access operations -/

theorem containsₘ_eq_containsKey [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.containsₘ a = containsKey a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.contains_eq (fun _ => List.containsKey_of_perm)
    List.containsKey_append_of_not_contains_right

theorem contains_eq_containsKey [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.contains a = containsKey a (toListModel m.1.buckets) := by
  rw [contains_eq_containsₘ, containsₘ_eq_containsKey hm]

theorem get?ₘ_eq_getValueCast? [BEq α] [Hashable α] [LawfulBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.get?ₘ a = getValueCast? a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.getCast?_eq List.getValueCast?_of_perm
    List.getValueCast?_append_of_containsKey_eq_false

theorem get?_eq_getValueCast? [BEq α] [Hashable α] [LawfulBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.get? a = getValueCast? a (toListModel m.1.buckets) := by
  rw [get?_eq_get?ₘ, get?ₘ_eq_getValueCast? hm]

theorem getₘ_eq_getValue [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {h : m.containsₘ a} :
    m.getₘ a h = getValueCast a (toListModel m.1.buckets) (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.getCast List.getValueCast AssocList.getCast_eq
    List.getValueCast_of_perm List.getValueCast_append_of_containsKey_eq_false

theorem getEntryₘ_eq_getEntry [BEq α] [PartialEquivBEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {h : m.containsₘ a} :
    m.getEntryₘ a h = List.getEntry a (toListModel m.1.buckets) (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.getEntry List.getEntry AssocList.getEntry_eq getEntry_of_perm getEntry_append_of_containsKey_eq_false

theorem getEntry?ₘ_eq_getEntry? [BEq α] [PartialEquivBEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} :
    m.getEntry?ₘ a = List.getEntry? a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.getEntry?_eq getEntry?_of_perm getEntry?_append_of_containsKey_eq_false

theorem get_eq_getValueCast [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {h : m.contains a} :
    m.get a h = getValueCast a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) := by
  rw [get_eq_getₘ, getₘ_eq_getValue hm]

theorem getEntry_eq_getEntry [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {h : m.contains a} :
    m.getEntry a h = List.getEntry a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) := by
  rw [getEntry_eq_getEntryₘ, getEntryₘ_eq_getEntry hm]

theorem getEntry?_eq_getEntry? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} :
    m.getEntry? a = List.getEntry? a (toListModel m.1.buckets) := by
  rw [getEntry?_eq_getEntry?ₘ, getEntry?ₘ_eq_getEntry? hm]

theorem getEntryDₘ_eq_getEntryD [BEq α] [PartialEquivBEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {fallback : (a : α) × β a} :
    m.getEntryDₘ a fallback = List.getEntryD a fallback (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.getEntryD_eq getEntryD_of_perm getEntryD_append_of_containsKey_eq_false

theorem getEntryD_eq_getEntryD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {fallback : (a : α) × β a} :
    m.getEntryD a fallback = List.getEntryD a fallback (toListModel m.1.buckets) := by
  rw [getEntryD_eq_getEntryDₘ, getEntryDₘ_eq_getEntryD hm]

theorem getEntry!ₘ_eq_getEntry! [BEq α] [PartialEquivBEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} [Inhabited ((a : α) × β a)] :
    m.getEntry!ₘ a = List.getEntry! a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.getEntry!_eq getEntry!_of_perm getEntry!_append_of_containsKey_eq_false

theorem getEntry!_eq_getEntry! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} [Inhabited ((a : α) × β a)] :
    m.getEntry! a = List.getEntry! a (toListModel m.1.buckets) := by
  rw [getEntry!_eq_getEntry!ₘ, getEntry!ₘ_eq_getEntry! hm]

theorem get!ₘ_eq_getValueCast! [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} [Inhabited (β a)] :
    m.get!ₘ a = getValueCast! a (toListModel m.1.buckets) := by
  rw [get!ₘ, get?ₘ_eq_getValueCast? hm, List.getValueCast!_eq_getValueCast?]

theorem get!_eq_getValueCast! [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} [Inhabited (β a)] : m.get! a = getValueCast! a (toListModel m.1.buckets) := by
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValueCast! hm]

theorem getDₘ_eq_getValueCastD [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} {fallback : β a} :
    m.getDₘ a fallback = getValueCastD a (toListModel m.1.buckets) fallback := by
  rw [getDₘ, get?ₘ_eq_getValueCast? hm, List.getValueCastD_eq_getValueCast?]

theorem getD_eq_getValueCastD [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (hm : Raw.WFImp m.1)
    {a : α} {fallback : β a} :
    m.getD a fallback = getValueCastD a (toListModel m.1.buckets) fallback := by
  rw [getD_eq_getDₘ, getDₘ_eq_getValueCastD hm]

theorem getKey?ₘ_eq_getKey? [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} :
    m.getKey?ₘ a = List.getKey? a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.getKey?_eq List.getKey?_of_perm List.getKey?_append_of_containsKey_eq_false

theorem getKey?_eq_getKey? [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} :
    m.getKey? a = List.getKey? a (toListModel m.1.buckets) := by
  rw [getKey?_eq_getKey?ₘ, getKey?ₘ_eq_getKey? hm]

theorem getKeyₘ_eq_getKey [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    m.getKeyₘ a (by exact h) = List.getKey a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.getKey List.getKey AssocList.getKey_eq
    List.getKey_of_perm List.getKey_append_of_containsKey_eq_false

theorem getKey_eq_getKey [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    m.getKey a h = List.getKey a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) := by
  rw [getKey_eq_getKeyₘ, getKeyₘ_eq_getKey hm]

theorem getKey!ₘ_eq_getKey! [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getKey!ₘ a = List.getKey! a (toListModel m.1.buckets) := by
  rw [getKey!ₘ, getKey?ₘ_eq_getKey? hm, List.getKey!_eq_getKey?]

theorem getKey!_eq_getKey! [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [Inhabited α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getKey! a = List.getKey! a (toListModel m.1.buckets) := by
  rw [getKey!_eq_getKey!ₘ, getKey!ₘ_eq_getKey! hm]

theorem getKeyDₘ_eq_getKeyD [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a fallback : α} :
    m.getKeyDₘ a fallback = List.getKeyD a (toListModel m.1.buckets) fallback := by
  rw [getKeyDₘ, getKey?ₘ_eq_getKey? hm, List.getKeyD_eq_getKey?]

theorem getKeyD_eq_getKeyD [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a fallback : α} :
    m.getKeyD a fallback = List.getKeyD a (toListModel m.1.buckets) fallback := by
  rw [getKeyD_eq_getKeyDₘ, getKeyDₘ_eq_getKeyD hm]

section

variable {β : Type v}

theorem Const.get?ₘ_eq_getValue? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} :
    Const.get?ₘ m a = getValue? a (toListModel m.1.buckets) :=
  apply_bucket hm AssocList.get?_eq List.getValue?_of_perm getValue?_append_of_containsKey_eq_false

theorem Const.get?_eq_getValue? [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} :
    Const.get? m a = getValue? a (toListModel m.1.buckets) := by
  rw [Const.get?_eq_get?ₘ, Const.get?ₘ_eq_getValue? hm]

theorem Const.getₘ_eq_getValue [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} {h} :
    Const.getₘ m a h = getValue a (toListModel m.1.buckets) (containsₘ_eq_containsKey hm ▸ h) :=
  apply_bucket_with_proof hm a AssocList.get List.getValue AssocList.get_eq List.getValue_of_perm
    List.getValue_append_of_containsKey_eq_false

theorem Const.get_eq_getValue [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} {h} :
    Const.get m a h = getValue a (toListModel m.1.buckets) (contains_eq_containsKey hm ▸ h) := by
  rw [Const.get_eq_getₘ, Const.getₘ_eq_getValue hm]

theorem Const.get!ₘ_eq_getValue! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    [Inhabited β] {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} :
    Const.get!ₘ m a = getValue! a (toListModel m.1.buckets) := by
  rw [get!ₘ, get?ₘ_eq_getValue? hm, List.getValue!_eq_getValue?]

theorem Const.get!_eq_getValue! [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    [Inhabited β] {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} :
    Const.get! m a = getValue! a (toListModel m.1.buckets) := by
  rw [get!_eq_get!ₘ, get!ₘ_eq_getValue! hm]

theorem Const.getDₘ_eq_getValueD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} {fallback : β} :
    Const.getDₘ m a fallback = getValueD a (toListModel m.1.buckets) fallback := by
  rw [getDₘ, get?ₘ_eq_getValue? hm, List.getValueD_eq_getValue?]

theorem Const.getD_eq_getValueD [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (hm : Raw.WFImp m.1) {a : α} {fallback : β} :
    Const.getD m a fallback = getValueD a (toListModel m.1.buckets) fallback := by
  rw [getD_eq_getDₘ, getDₘ_eq_getValueD hm]

end

/-! # `replaceₘ` -/

theorem toListModel_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
   (h : Raw.WFImp m.1) (a : α) (b : β a) :
  Perm (toListModel (m.replaceₘ a b).1.buckets) (replaceEntry a b (toListModel m.1.2)) :=
  toListModel_updateBucket h (.of_eq AssocList.toList_replace) List.replaceEntry_of_perm
    List.replaceEntry_append_of_containsKey_right_eq_false

theorem isHashSelf_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) (a : α) (b : β a) : IsHashSelf (m.replaceₘ a b).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  exact Or.inl (by simpa using containsKey_of_mem hp)

theorem wfImp_replaceₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) (a : α) (b : β a) : Raw.WFImp (m.replaceₘ a b).1 where
  buckets_hash_self := isHashSelf_replaceₘ m h a b
  size_eq := h.size_eq.trans
    (Eq.trans length_replaceEntry.symm (toListModel_replaceₘ _ h _ _).length_eq.symm)
  distinct := h.distinct.replaceEntry.perm (toListModel_replaceₘ _ h _ _)

/-! # `insertₘ` -/

theorem toListModel_consₘ [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) (b : β a) :
    Perm (toListModel (m.consₘ a b).1.buckets) (⟨a, b⟩ :: (toListModel m.1.2)) :=
  toListModel_updateBucket h .rfl (fun _ => Perm.cons _) (fun _ => cons_append)

theorem isHashSelf_consₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) (a : α) (b : β a) : IsHashSelf (m.consₘ a b).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  simp only [AssocList.toList_cons, mem_cons] at hp
  rcases hp with (rfl|hp)
  · exact Or.inr rfl
  · exact Or.inl (containsKey_of_mem hp)

theorem wfImp_consₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) (a : α) (b : β a) (hc : m.containsₘ a = false) :
    Raw.WFImp (m.consₘ a b).1 where
  buckets_hash_self := isHashSelf_consₘ m h a b
  size_eq := by
    refine Eq.trans ?_ (toListModel_consₘ _ h _ _).length_eq.symm
    simpa [consₘ] using h.size_eq
  distinct := by
    refine (h.distinct.cons ?_).perm (toListModel_consₘ _ h _ _)
    rwa [← containsₘ_eq_containsKey h]

theorem toListModel_insertₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Perm (toListModel (m.insertₘ a b).1.2) (insertEntry a b (toListModel m.1.2)) := by
  rw [insertₘ]
  split
  next h' =>
    rw [containsₘ_eq_containsKey h] at h'
    rw [insertEntry_of_containsKey h']
    exact toListModel_replaceₘ _ h _ _
  next h' =>
    rw [containsₘ_eq_containsKey h, Bool.not_eq_true] at h'
    rw [insertEntry_of_containsKey_eq_false h']
    refine (Raw₀.toListModel_expandIfNecessary _).trans ?_
    exact toListModel_consₘ m h a b

theorem wfImp_insertₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} : Raw.WFImp (m.insertₘ a b).1 := by
  rw [insertₘ]
  split
  · apply wfImp_replaceₘ _ h
  · apply wfImp_expandIfNecessary
    apply wfImp_consₘ _ h _ _ (by simp_all)

/-! # `insert` -/

theorem toListModel_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Perm (toListModel (m.insert a b).1.2) (insertEntry a b (toListModel m.1.2)) := by
  rw [insert_eq_insertₘ]
  exact toListModel_insertₘ h

theorem wfImp_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} : Raw.WFImp (m.insert a b).1 := by
  rw [insert_eq_insertₘ]
  exact wfImp_insertₘ h

/-! # `alter` -/

theorem toListModel_updateBucket_alter [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {f : Option (β a) → Option (β a)} :
    Perm (toListModel (updateBucket m.1.buckets m.2 a (AssocList.alter a f)))
      (alterKey a f (toListModel m.1.buckets)) := by
  exact toListModel_updateBucket h AssocList.toList_alter List.alterKey_of_perm
    List.alterKey_append_of_containsKey_right_eq_false

theorem isHashSelf_updateBucket_alter [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {f : Option (β a) → Option (β a)} :
    IsHashSelf (updateBucket m.1.buckets m.2 a (AssocList.alter a f)) := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  rw [AssocList.toList_alter.mem_iff] at hp
  by_cases h : p.fst = a
  · exact .inr <| congrArg hash h
  · rw [mem_alterKey_of_key_ne _ h] at hp
    exact .inl <| containsKey_of_mem hp

theorem wfImp_updateBucket_alter [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {f : Option (β a) → Option (β a)} :
    Raw.WFImp (withComputedSize <| updateBucket m.1.buckets m.2 a (AssocList.alter a f)) where
  buckets_hash_self := isHashSelf_updateBucket_alter h
  size_eq := by rw [size_withComputedSize, computeSize_eq, buckets_withComputedSize]
  distinct := DistinctKeys.perm (toListModel_updateBucket_alter h) h.distinct.alterKey

theorem isHashSelf_alterₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (h : Raw.WFImp m.1)
    (a : α) (f : Option (β a) → Option (β a)) : IsHashSelf (m.alterₘ a f).1.buckets := by
  dsimp only [alterₘ, withComputedSize]
  split
  · exact isHashSelf_updateBucket_alter h
  next hc =>
    split
    · exact h.buckets_hash_self
    · refine (wfImp_expandIfNecessary _ (wfImp_consₘ _ h _ _ ?_)).buckets_hash_self
      exact Bool.not_eq_true _ ▸ hc

theorem toListModel_alterₘ [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (h : Raw.WFImp m.1)
    {a : α} {f : Option (β a) → Option (β a)} :
    Perm (toListModel (m.alterₘ a f).1.2) (alterKey a f (toListModel m.1.2)) := by
  rw [alterₘ]
  split
  · exact toListModel_updateBucket_alter h
  next hc =>
    rw [Bool.not_eq_true, containsₘ_eq_containsKey h] at hc
    rw [alterKey, getValueCast?_eq_none hc]
    split
    next hn =>
      simp only [hn]
      rw [eraseKey_of_containsKey_eq_false]
      exact hc
    next hs =>
      simp only [hs]
      refine Perm.trans (toListModel_expandIfNecessary _) ?_
      refine Perm.trans (toListModel_consₘ m h _ _) ?_
      rw [insertEntry_of_containsKey_eq_false]
      exact hc

theorem toListModel_alter [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (h : Raw.WFImp m.1)
    {a : α} {f : Option (β a) → Option (β a)} :
    Perm (toListModel (m.alter a f).1.2) (alterKey a f (toListModel m.1.2)) := by
  rw [alter_eq_alterₘ]
  exact toListModel_alterₘ h

theorem wfImp_alterₘ [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α}
    {f : Option (β a) → Option (β a)} : Raw.WFImp (m.alterₘ a f).1 where
  buckets_hash_self := isHashSelf_alterₘ m h a f
  distinct := DistinctKeys.perm (toListModel_alterₘ h) h.distinct.alterKey
  size_eq := by
    rw [← Perm.length_eq (toListModel_alterₘ h).symm, alterₘ]
    split
    next h₁ =>
      rw [containsₘ_eq_containsKey h] at h₁
      simp only [length_alterKey, h.size_eq, dif_pos h₁]
      rw [containsₘ_eq_containsKey (by apply wfImp_updateBucket_alter h)]
      simp only [buckets_withComputedSize]
      simp only [containsKey_of_perm <| toListModel_updateBucket_alter h]
      rw [← getValueCast?_eq_some_getValueCast h₁]
      conv => lhs; congr; rw [containsKey_alterKey_self h.distinct]
    next h₁ =>
      rw [containsₘ_eq_containsKey h] at h₁
      rw [alterKey]
      rw [getValueCast?_eq_none <| Bool.not_eq_true _ ▸ h₁]
      split
      next heq =>
        rw [heq, h.size_eq, length_eraseKey, if_neg h₁]
      next heq =>
        rw [heq, size_expandIfNecessary, consₘ, length_insertEntry, if_neg h₁, h.size_eq]

theorem wfImp_alter [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {f : Option (β a) → Option (β a)} : Raw.WFImp (m.alter a f).1 := by
  rw [alter_eq_alterₘ]
  exact wfImp_alterₘ h

namespace Const

variable {β : Type v}

theorem toListModel_updateBucket_alter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} :
    Perm (toListModel (updateBucket m.1.buckets m.2 a (AssocList.Const.alter a f)))
      (Const.alterKey a f (toListModel m.1.buckets)) := by
  exact toListModel_updateBucket h AssocList.Const.toList_alter List.Const.alterKey_of_perm
    List.Const.alterKey_append_of_containsKey_right_eq_false

theorem isHashSelf_updateBucket_alter [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} :
    IsHashSelf (updateBucket m.1.buckets m.2 a (AssocList.Const.alter a f)) := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  rw [AssocList.Const.toList_alter.mem_iff] at hp
  by_cases h : p.fst == a
  · exact .inr <| hash_eq h
  · rw [Bool.not_eq_true] at h
    rw [Const.mem_alterKey_of_key_not_beq _ h] at hp
    exact .inl <| containsKey_of_mem hp

theorem wfImp_updateBucket_alter [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} :
    Raw.WFImp (withComputedSize <| updateBucket m.1.buckets m.2 a (AssocList.Const.alter a f)) where
  buckets_hash_self := isHashSelf_updateBucket_alter h
  size_eq := by rw [size_withComputedSize, computeSize_eq]; rfl
  distinct := DistinctKeys.perm (toListModel_updateBucket_alter h) h.distinct.constAlterKey

theorem isHashSelf_alterₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m : Raw₀ α (fun _ => β)) (h : Raw.WFImp m.1) (a : α) (f : Option β → Option β) :
  IsHashSelf (Const.alterₘ m a f).1.buckets := by
  dsimp only [alterₘ, withComputedSize]
  split
  · exact isHashSelf_updateBucket_alter h
  next hc =>
    split
    · exact h.buckets_hash_self
    · refine (wfImp_expandIfNecessary _ (wfImp_consₘ _ h _ _ ?_)).buckets_hash_self
      exact Bool.not_eq_true _ ▸ hc

theorem toListModel_alterₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} :
    Perm (toListModel (Const.alterₘ m a f).1.2) (Const.alterKey a f (toListModel m.1.2)) := by
  rw [Const.alterₘ]
  split
  · exact toListModel_updateBucket_alter h
  next hc =>
    rw [Bool.not_eq_true, containsₘ_eq_containsKey h] at hc
    rw [Const.alterKey, getValue?_eq_none.mpr hc]
    split
    next hn =>
      simp only [hn]
      rw [eraseKey_of_containsKey_eq_false]
      exact hc
    next hs =>
      simp only [hs]
      refine Perm.trans (toListModel_expandIfNecessary _) ?_
      refine Perm.trans (toListModel_consₘ m h _ _) ?_
      rw [insertEntry_of_containsKey_eq_false]
      exact hc

theorem toListModel_alter [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => β)} (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} :
    Perm (toListModel (Const.alter m a f).1.2) (Const.alterKey a f (toListModel m.1.2)) := by
  rw [alter_eq_alterₘ]
  exact toListModel_alterₘ h

theorem wfImp_alterₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} : Raw.WFImp (Const.alterₘ m a f).1 where
  buckets_hash_self := isHashSelf_alterₘ m h a f
  distinct := DistinctKeys.perm (toListModel_alterₘ h) h.distinct.constAlterKey
  size_eq := by
    rw [← Perm.length_eq (toListModel_alterₘ h).symm, alterₘ]
    split
    next h₁ =>
      rw [containsₘ_eq_containsKey h] at h₁
      simp only [Const.length_alterKey, h.size_eq, dif_pos h₁]
      rw [containsₘ_eq_containsKey (by apply wfImp_updateBucket_alter h)]
      simp only [buckets_withComputedSize]
      simp only [containsKey_of_perm <| toListModel_updateBucket_alter h]
      rw [← getValue?_eq_some_getValue h₁]
      conv => lhs; congr; rw [Const.containsKey_alterKey_self h.distinct]
    next h₁ =>
      rw [containsₘ_eq_containsKey h] at h₁
      rw [Const.alterKey]
      rw [getValue?_eq_none.mpr <| Bool.not_eq_true _ ▸ h₁]
      split
      next heq =>
        rw [heq, h.size_eq, length_eraseKey, if_neg h₁]
      next heq =>
        rw [heq, size_expandIfNecessary, consₘ, length_insertEntry, if_neg h₁, h.size_eq]

theorem wfImp_alter [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] {m : Raw₀ α (fun _ => β)}
    (h : Raw.WFImp m.1) {a : α} {f : Option β → Option β} : Raw.WFImp (Const.alter m a f).1 := by
  rw [Const.alter_eq_alterₘ]
  exact wfImp_alterₘ h

end Const

/-! # `modify` -/

theorem toListModel_modify [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (h : Raw.WFImp m.1)
    {a : α} {f : β a → β a} :
    Perm (toListModel (m.modify a f).1.2) (modifyKey a f (toListModel m.1.2)) := by
  rw [modify_eq_alter, modifyKey_eq_alterKey]
  exact toListModel_alter h

theorem wfImp_modifyₘ [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {f : β a → β a} : Raw.WFImp (m.modifyₘ a f).1 := wfImp_alterₘ h

theorem wfImp_modify [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α}
    {f : β a → β a} : Raw.WFImp (m.modify a f).1 := by
  rw [modify_eq_modifyₘ]
  exact wfImp_alterₘ h

namespace Const

variable {β : Type v} {m : Raw₀ α (fun _ => β)}

theorem toListModel_modify [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (h : Raw.WFImp m.1)
    {a : α} {f : β → β} :
    Perm (toListModel (Const.modify m a f).1.2) (Const.modifyKey a f (toListModel m.1.2)) := by
  rw [Const.modify_eq_alter, Const.modifyKey_eq_alterKey]
  exact Const.toListModel_alter h

theorem wfImp_modifyₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (h : Raw.WFImp m.1) {a : α} {f : β → β} : Raw.WFImp (Const.modifyₘ m a f).1 :=
  Const.wfImp_alterₘ h

theorem wfImp_modify [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (h : Raw.WFImp m.1) {a : α} {f : β → β} : Raw.WFImp (Const.modify m a f).1 := by
  rw [Const.modify_eq_modifyₘ]
  exact wfImp_alterₘ h

end Const

/-! # `containsThenInsert` -/

theorem toListModel_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Perm (toListModel (m.containsThenInsert a b).2.1.2) (insertEntry a b (toListModel m.1.2)) := by
  rw [containsThenInsert_eq_insertₘ]
  exact toListModel_insertₘ h

theorem wfImp_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} : Raw.WFImp (m.containsThenInsert a b).2.1 := by
  rw [containsThenInsert_eq_insertₘ]
  exact wfImp_insertₘ h

/-! # `insertIfNewₘ` -/

theorem toListModel_insertIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Perm (toListModel (m.insertIfNewₘ a b).1.buckets)
      (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [insertIfNewₘ, insertEntryIfNew, containsₘ_eq_containsKey h, cond_eq_ite]
  split
  next h' => exact Perm.refl _
  next h' => exact (toListModel_expandIfNecessary _).trans (toListModel_consₘ m h a b)

theorem wfImp_insertIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} : Raw.WFImp (m.insertIfNewₘ a b).1 := by
  rw [insertIfNewₘ]
  split
  · exact h
  · apply wfImp_expandIfNecessary
    apply wfImp_consₘ _ h _ _ (by simp_all)

/-! # `insertIfNew` -/

theorem toListModel_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Perm (toListModel (m.insertIfNew a b).1.buckets)
      (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [insertIfNew_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (h : Raw.WFImp m.1) {a : α} {b : β a} : Raw.WFImp (m.insertIfNew a b).1 := by
  rw [insertIfNew_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `containsThenInsertIfNew` -/

theorem toListModel_containsThenInsertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Perm (toListModel (m.containsThenInsertIfNew a b).2.1.2)
      (insertEntryIfNew a b (toListModel m.1.2)) := by
  rw [containsThenInsertIfNew_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_containsThenInsertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
      Raw.WFImp (m.containsThenInsertIfNew a b).2.1 := by
  rw [containsThenInsertIfNew_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `getThenInsertIfNew?` -/

theorem toListModel_getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α}
    {b : β a} (h : Raw.WFImp m.1) :
    Perm (toListModel (m.getThenInsertIfNew? a b).2.1.buckets)
      (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem wfImp_getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw₀ α β} {a : α}
    {b : β a} (h : Raw.WFImp m.1) : Raw.WFImp (m.getThenInsertIfNew? a b).2.1 := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `Const.getThenInsertIfNew?` -/

theorem Const.toListModel_getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] {m : Raw₀ α (fun _ => β)} {a : α} {b : β} (h : Raw.WFImp m.1) :
    Perm (toListModel (Const.getThenInsertIfNew? m a b).2.1.buckets)
      (insertEntryIfNew a b (toListModel m.1.buckets)) := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact toListModel_insertIfNewₘ h

theorem Const.wfImp_getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] {m : Raw₀ α (fun _ => β)} {a : α} {b : β} (h : Raw.WFImp m.1) :
    Raw.WFImp (Const.getThenInsertIfNew? m a b).2.1 := by
  rw [getThenInsertIfNew?_eq_insertIfNewₘ]
  exact wfImp_insertIfNewₘ h

/-! # `eraseₘ` -/

theorem toListModel_eraseₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (a : α) (h : Raw.WFImp m.1) :
    Perm (toListModel (m.eraseₘaux a).1.buckets) (eraseKey a (toListModel m.1.buckets)) :=
  toListModel_updateBucket h (.of_eq AssocList.toList_erase) List.eraseKey_of_perm
    List.eraseKey_append_of_containsKey_right_eq_false

theorem isHashSelf_eraseₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β)
    (a : α) (h : Raw.WFImp m.1) : IsHashSelf (m.eraseₘaux a).1.buckets := by
  apply h.buckets_hash_self.updateBucket (fun l p hp => ?_)
  rw [AssocList.toList_erase] at hp
  exact Or.inl (containsKey_of_mem ((sublist_eraseKey.mem hp)))

theorem wfImp_eraseₘaux [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (m : Raw₀ α β) (a : α)
    (h : Raw.WFImp m.1) (h' : m.containsₘ a = true) : Raw.WFImp (m.eraseₘaux a).1 where
  buckets_hash_self := isHashSelf_eraseₘaux m a h
  size_eq := by
    rw [(toListModel_eraseₘaux m a h).length_eq, eraseₘaux, length_eraseKey,
      ← containsₘ_eq_containsKey h, h']
    simp [h.size_eq]
  distinct := h.distinct.eraseKey.perm (toListModel_eraseₘaux m a h)

theorem toListModel_perm_eraseKey_of_containsₘ_eq_false [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m : Raw₀ α β) (a : α) (h : Raw.WFImp m.1) (h' : m.containsₘ a = false) :
    Perm (toListModel m.1.buckets) (eraseKey a (toListModel m.1.buckets)) := by
  rw [eraseKey_of_containsKey_eq_false]
  rw [← containsₘ_eq_containsKey h, h']

theorem toListModel_eraseₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {a : α} (h : Raw.WFImp m.1) :
    Perm (toListModel (m.eraseₘ a).1.buckets) (eraseKey a (toListModel m.1.buckets)) := by
  rw [eraseₘ]
  split
  · exact toListModel_eraseₘaux m a h
  next h' =>
    exact toListModel_perm_eraseKey_of_containsₘ_eq_false _ _ h (eq_false_of_ne_true h')

theorem wfImp_eraseₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : Raw.WFImp m.1) : Raw.WFImp (m.eraseₘ a).1 := by
  rw [eraseₘ]
  split
  next h' => exact wfImp_eraseₘaux m a h h'
  · exact h

/-! # `erase` -/

theorem toListModel_erase [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {a : α} (h : Raw.WFImp m.1) :
    Perm (toListModel (m.erase a).1.buckets) (eraseKey a (toListModel m.1.buckets)) := by
  rw [erase_eq_eraseₘ]
  exact toListModel_eraseₘ h

theorem wfImp_erase [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β} {a : α}
    (h : Raw.WFImp m.1) : Raw.WFImp (m.erase a).1 := by
  rw [erase_eq_eraseₘ]
  exact wfImp_eraseₘ h

/-! # `filterₘ` -/

theorem toListModel_filterₘ {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    Perm (toListModel (m.filterₘ f).1.buckets)
      ((toListModel m.1.buckets).filter fun p => f p.1 p.2) :=
  toListModel_updateAllBuckets AssocList.toList_filter (by simp)

theorem isHashSelf_filterₘ [BEq α] [Hashable α] [ReflBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Bool} (h : Raw.WFImp m.1) : IsHashSelf (m.filterₘ f).1.buckets := by
  refine h.buckets_hash_self.updateAllBuckets (fun l p hp => ?_)
  have hp := AssocList.toList_filter.mem_iff.1 hp
  obtain ⟨hp, -⟩ := mem_filter.1 hp
  exact containsKey_of_mem hp

theorem wfImp_filterₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Bool} (h : Raw.WFImp m.1) : Raw.WFImp (m.filterₘ f).1 where
  buckets_hash_self := isHashSelf_filterₘ h
  size_eq := by simp [filterₘ]
  distinct := h.distinct.filter.perm toListModel_filterₘ

/-! # `filter` -/

theorem toListModel_filter {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    Perm (toListModel (m.filter f).1.buckets)
      ((toListModel m.1.buckets).filter fun p => f p.1 p.2) := by
  rw [filter_eq_filterₘ]
  exact toListModel_filterₘ

theorem wfImp_filter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Bool} (h : Raw.WFImp m.1) : Raw.WFImp (m.filter f).1 := by
  rw [filter_eq_filterₘ]
  exact wfImp_filterₘ h

/-! # `insertListₘ` -/

theorem toListModel_insertListₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} (h : Raw.WFImp m.1) :
    Perm (toListModel (insertListₘ m l).1.buckets)
      (List.insertList (toListModel m.1.buckets) l) := by
  induction l generalizing m with
  | nil =>
    simp [insertListₘ, List.insertList]
  | cons hd tl ih =>
    simp only [insertListₘ, List.insertList]
    apply Perm.trans (ih (wfImp_insert h))
    apply List.insertList_perm_of_perm_first (toListModel_insert h) (wfImp_insert h).distinct

theorem toListModel_eraseListₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List α} (h : Raw.WFImp m.1) :
    Perm (toListModel (eraseListₘ m l).1.buckets)
      (List.eraseList (toListModel m.1.buckets) l) := by
  induction l generalizing m with
  | nil =>
    simp [eraseListₘ, List.eraseList]
  | cons hd tl ih =>
    simp only [eraseListₘ, List.eraseList]
    apply Perm.trans (ih (wfImp_erase h))
    apply List.eraseList_perm_of_perm_first (toListModel_erase h) (wfImp_erase h).distinct

/-! # `insertListₘ` -/

theorem toListModel_insertListIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} (h : Raw.WFImp m.1) :
    Perm (toListModel (insertListIfNewₘ m l).1.buckets)
      (List.insertListIfNew (toListModel m.1.buckets) l) := by
  induction l generalizing m with
  | nil =>
    simp [insertListIfNewₘ, List.insertListIfNew]
  | cons hd tl ih =>
    simp only [insertListIfNewₘ, List.insertListIfNew]
    apply Perm.trans (ih (wfImp_insertIfNew h))
    apply List.insertListIfNew_perm_of_perm_first (toListModel_insertIfNew h) (wfImp_insertIfNew h).distinct

/-! # `unionₘ` -/

theorem insertMany_eq_insertListₘ_toListModel [BEq α] [Hashable α] (m m₂ : Raw₀ α β) :
    insertMany m m₂.1 = insertListₘ m (toListModel m₂.1.buckets) := by
  simp only [insertMany, bind_pure_comp, map_pure, bind_pure]
  simp only [ForIn.forIn]
  simp only [Raw.forIn_eq_forIn_toListModel, forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize toListModel m₂.val.buckets = l
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
    (∀ {m'' : Raw₀ α β} {a : α} {b : β a}, P m'' → P (m''.insert a b)) → P m → P m' }),
      (List.foldl (fun m' p => ⟨m'.val.insert p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
    t.val.insertListₘ l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, insertListₘ]
    apply ih

theorem insertMany_array_eq_insertMany_toList [BEq α] [Hashable α] (m : Raw₀ α β) (a : Array ((k : α) × (β k))) :
    insertMany m a = insertMany m a.toList := by
  simp only [insertMany, bind_pure_comp, map_pure, bind_pure, ← Array.forIn_toList, forIn_pure_yield_eq_foldl, Array.foldl_toList, Id.run_pure]

theorem Const.insertMany_array_eq_insertMany_toList [BEq α] [Hashable α] {β : Type v} (m : Raw₀ α fun _ => β) (a : Array (α × β)) :
    Const.insertMany m a = Const.insertMany m a.toList := by
  simp only [insertMany, bind_pure_comp, map_pure, bind_pure, ← Array.forIn_toList, forIn_pure_yield_eq_foldl, Array.foldl_toList, Id.run_pure]

theorem Const.insertManyIfNewUnit_array_eq_insertManyIfNewUnit_toList [BEq α] [Hashable α] (m : Raw₀ α fun _ => Unit) (a : Array α) :
    Const.insertManyIfNewUnit m a = Const.insertManyIfNewUnit m a.toList := by
  simp only [insertManyIfNewUnit, bind_pure_comp, map_pure, bind_pure, ← Array.forIn_toList, forIn_pure_yield_eq_foldl, Array.foldl_toList, Id.run_pure]

theorem insertManyIfNew_eq_insertListIfNewₘ_toListModel [BEq α] [Hashable α] (m m₂ : Raw₀ α β) :
    insertManyIfNew m m₂.1 = insertListIfNewₘ m (toListModel m₂.1.buckets) := by
  simp only [insertManyIfNew, bind_pure_comp, map_pure, bind_pure]
  simp only [ForIn.forIn]
  simp only [Raw.forIn_eq_forIn_toListModel, forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize toListModel m₂.val.buckets = l
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
    (∀ {m'' : Raw₀ α β} {a : α} {b : β a}, P m'' → P (m''.insertIfNew a b)) → P m → P m' }),
      (List.foldl (fun m' p => ⟨m'.val.insertIfNew p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
    t.val.insertListIfNewₘ l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListIfNewₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih

theorem union_eq_unionₘ [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) :
    union m₁ m₂ = unionₘ m₁ m₂ := by
  rw [union, unionₘ]
  split
  · rw [insertManyIfNew_eq_insertListIfNewₘ_toListModel]
  · rw [insertMany_eq_insertListₘ_toListModel]

theorem toListModel_unionₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw₀ α β} (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    Perm (toListModel (unionₘ m₁ m₂).1.buckets)
      (List.insertList (toListModel m₁.1.buckets) (toListModel m₂.1.buckets)) := by
  refine Perm.trans ?_ (Perm.symm (List.insertList_perm_insertSmallerList h₁.distinct h₂.distinct))
  rw [unionₘ, insertSmallerList, h₁.size_eq, h₂.size_eq]
  split
  · exact toListModel_insertListIfNewₘ ‹_›
  · exact toListModel_insertListₘ ‹_›

theorem wfImp_inter [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    {m₁ m₂ : Raw α β} {h₁ : 0 < m₁.buckets.size} {h₂ : 0 < m₂.buckets.size} (wh₁ : Raw.WFImp m₁) :
    Raw.WFImp (Raw₀.inter ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).val := by
  rw [inter]
  split
  · apply wfImp_filter wh₁
  · rw [interSmaller]
    apply @Raw.fold_induction _ β _ (fun sofar k x => interSmallerFn ⟨m₁, h₁⟩ sofar k) emptyWithCapacity m₂ (Raw.WFImp ·.val) wfImp_emptyWithCapacity
    intro acc a b wf
    rw [interSmallerFn]
    split
    · apply wfImp_insert wf
    · apply wf

end Raw₀

namespace Raw

theorem WF.out [BEq α] [Hashable α] [i₁ : EquivBEq α] [i₂ : LawfulHashable α] {m : Raw α β}
    (h : m.WF) : Raw.WFImp m := by
  induction h generalizing i₁ i₂ with
  | wf _ h => apply h
  | emptyWithCapacity₀ => exact Raw₀.wfImp_emptyWithCapacity
  | insert₀ _ h => exact Raw₀.wfImp_insert (by apply h)
  | containsThenInsert₀ _ h => exact Raw₀.wfImp_containsThenInsert (by apply h)
  | containsThenInsertIfNew₀ _ h => exact Raw₀.wfImp_containsThenInsertIfNew (by apply h)
  | erase₀ _ h => exact Raw₀.wfImp_erase (by apply h)
  | insertIfNew₀ _ h => exact Raw₀.wfImp_insertIfNew (by apply h)
  | getThenInsertIfNew?₀ _ h => exact Raw₀.wfImp_getThenInsertIfNew? (by apply h)
  | filter₀ _ h => exact Raw₀.wfImp_filter (by apply h)
  | constGetThenInsertIfNew?₀ _ h => exact Raw₀.Const.wfImp_getThenInsertIfNew? (by apply h)
  | modify₀ _ h => exact Raw₀.wfImp_modify (by apply h)
  | constModify₀ _ h => exact Raw₀.Const.wfImp_modify (by apply h)
  | alter₀ _ h => exact Raw₀.wfImp_alter (by apply h)
  | constAlter₀ _ h => exact Raw₀.Const.wfImp_alter (by apply h)
  | inter₀ _ _ h _  => exact Raw₀.wfImp_inter (by apply h)

end Raw

namespace Raw₀

/-! # `filterMapₘ` -/

theorem toListModel_filterMapₘ {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} :
    Perm (toListModel (m.filterMapₘ f).1.buckets)
      ((toListModel m.1.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) :=
  toListModel_updateAllBuckets AssocList.toList_filterMap
    (by simp [List.filterMap_append])

theorem isHashSelf_filterMapₘ [BEq α] [Hashable α] [ReflBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Option (δ a)} (h : Raw.WFImp m.1) :
    IsHashSelf (m.filterMapₘ f).1.buckets := by
  refine h.buckets_hash_self.updateAllBuckets (fun l p hp => ?_)
  have hp := AssocList.toList_filterMap.mem_iff.1 hp
  simp only [mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨p, ⟨hkv, ⟨d, ⟨-, rfl⟩⟩⟩⟩ := hp
  exact containsKey_of_mem hkv

theorem wfImp_filterMapₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Option (δ a)} (h : Raw.WFImp m.1) : Raw.WFImp (m.filterMapₘ f).1 where
  buckets_hash_self := isHashSelf_filterMapₘ h
  size_eq := by simp [filterMapₘ]
  distinct := h.distinct.filterMap.perm toListModel_filterMapₘ

/-! # `filterMap` -/

theorem toListModel_filterMap {m : Raw₀ α β} {f : (a : α) → β a → Option (δ a)} :
    Perm (toListModel (m.filterMap f).1.buckets)
      ((toListModel m.1.buckets).filterMap fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  rw [filterMap_eq_filterMapₘ]
  exact toListModel_filterMapₘ

theorem wfImp_filterMap [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → Option (δ a)} (h : Raw.WFImp m.1) :
    Raw.WFImp (m.filterMap f).1 := by
  rw [filterMap_eq_filterMapₘ]
  exact wfImp_filterMapₘ h

theorem wf_filterMap₀ [BEq α] [Hashable α] {m : Raw₀ α β} (h : m.1.WF)
    {f : (a : α) → β a → Option (δ a)} : (m.filterMap f).1.WF :=
  .wf (Raw₀.filterMap f ⟨m, h.size_buckets_pos⟩).2 (wfImp_filterMap (Raw.WF.out h))

theorem filterMap_eq_filter {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    m.filterMap (fun k => Option.guard (fun v => f k v)) = m.filter f := by
  rw [filter_eq_filterₘ, filterMap_eq_filterMapₘ, filterₘ, filterMapₘ]
  simp only [AssocList.filterMap_eq_filter]

theorem filterMap_eq_map [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {γ : α → Type w} (m : Raw₀ α β) (f : (a : α) → β a → γ a) (h : m.1.WF) :
    m.filterMap (fun k v => Option.some (f k v)) = m.map f := by
  rw [map_eq_mapₘ, filterMap_eq_filterMapₘ, mapₘ, filterMapₘ]
  simp only [AssocList.filterMap_eq_map, withComputedSize]
  simp only [computeSize_eq, Subtype.mk.injEq, Raw.mk.injEq, and_true]
  rw [(toListModel_updateAllBuckets (f := fun a => a.map f)
    AssocList.toList_map (by simp)).length_eq]
  rw [(Raw.WF.out h).size_eq, List.length_map]

/-! # `mapₘ` -/

theorem toListModel_mapₘ {m : Raw₀ α β} {f : (a : α) → β a → δ a} :
    Perm (toListModel (m.mapₘ f).1.buckets)
      ((toListModel m.1.buckets).map fun p => ⟨p.1, f p.1 p.2⟩) :=
  toListModel_updateAllBuckets AssocList.toList_map (by simp)

theorem isHashSelf_mapₘ [BEq α] [Hashable α] [ReflBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → δ a} (h : Raw.WFImp m.1) : IsHashSelf (m.mapₘ f).1.buckets := by
  refine h.buckets_hash_self.updateAllBuckets (fun l p hp => ?_)
  have hp := AssocList.toList_map.mem_iff.1 hp
  obtain ⟨p, hp₁, rfl⟩ := mem_map.1 hp
  exact containsKey_of_mem hp₁

theorem wfImp_mapₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → δ a} (h : Raw.WFImp m.1) : Raw.WFImp (m.mapₘ f).1 where
  buckets_hash_self := isHashSelf_mapₘ h
  size_eq := by rw [toListModel_mapₘ.length_eq, List.length_map, ← h.size_eq, mapₘ]
  distinct := h.distinct.map.perm toListModel_mapₘ

/-! # `map` -/

theorem toListModel_map {m : Raw₀ α β} {f : (a : α) → β a → δ a} :
    Perm (toListModel (m.map f).1.buckets)
      ((toListModel m.1.buckets).map fun p => ⟨p.1, f p.1 p.2⟩) := by
  rw [map_eq_mapₘ]
  exact toListModel_mapₘ

theorem wfImp_map [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    {f : (a : α) → β a → δ a} (h : Raw.WFImp m.1) : Raw.WFImp (m.map f).1 := by
  rw [map_eq_mapₘ]
  exact wfImp_mapₘ h

theorem wf_map₀ [BEq α] [Hashable α] {m : Raw₀ α β} (h : m.1.WF) {f : (a : α) → β a → δ a} :
    (m.map f).1.WF :=
  .wf (Raw₀.map f ⟨m, h.size_buckets_pos⟩).2 (Raw₀.wfImp_map (Raw.WF.out h))

/-! # `insertMany` -/

theorem wfImp_insertMany [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] {m : Raw₀ α β} {l : ρ} (h : Raw.WFImp m.1) :
    Raw.WFImp (m.insertMany l).1.1 :=
  Raw.WF.out ((m.insertMany l).2 _ Raw.WF.insert₀ (.wf m.2 h))

theorem toListModel_insertMany_list [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × (β a))} (h : Raw.WFImp m.1) :
    Perm (toListModel (insertMany m l).1.1.buckets)
      (List.insertList (toListModel m.1.buckets) l) := by
  rw [insertMany_eq_insertListₘ]
  apply toListModel_insertListₘ
  exact h

/-! # `eraseMany` -/

theorem WF.eraseManyEntries [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] {m : Raw α β}
    {l : ρ} (h : m.WF) : (m.eraseManyEntries l).WF := by
  simpa [Raw.eraseManyEntries, h.size_buckets_pos] using
    (Raw₀.eraseManyEntries ⟨m, h.size_buckets_pos⟩ l).2 _ Raw.WF.erase₀ h

theorem wf_insertMany₀ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] {m : Raw α β} {h : 0 < m.buckets.size} {l : ρ} (h' : m.WF) :
    (Raw₀.insertMany ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.insertMany ⟨m, h⟩ l).2 _ Raw.WF.insert₀ h'

theorem wf_eraseMany₀ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] {m : Raw α β} {h : 0 < m.buckets.size} {l : ρ} (h' : m.WF) :
    (eraseManyEntries ⟨m, h⟩ l).1.1.WF :=
  (eraseManyEntries ⟨m, h⟩ l).2 _ Raw.WF.erase₀ h'

theorem eraseMany_eq_eraseListₘ_toListModel [BEq α] [Hashable α] (m m₂ : Raw₀ α β) :
    eraseManyEntries m m₂.1 = eraseListₘ m ((toListModel m₂.1.buckets).map (·.1)) := by
  simp only [eraseManyEntries, bind_pure_comp, map_pure, bind_pure]
  simp only [ForIn.forIn]
  simp only [Raw.forIn_eq_forIn_toListModel, forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize toListModel m₂.val.buckets = l
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α}, P m'' → P (m''.erase a)) → P m → P m' }),
        (List.foldl (fun m' p => ⟨m'.val.erase p.1, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
      t.val.eraseListₘ (l.map (·.1)) from this _
  intro t
  induction l generalizing m with
  | nil => simp [eraseListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih

theorem toListModel_diffₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw₀ α β} (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    Perm (toListModel (diffₘ m₁ m₂).1.buckets)
      (List.filter (fun k => !List.contains ((toListModel m₂.1.buckets).map Sigma.fst) k.fst) (toListModel m₁.1.buckets)) := by
  rw [diffₘ]
  split
  · apply Perm.trans
    · apply toListModel_filterₘ
    · conv =>
        lhs
        lhs
        ext p
        congr
        rw [containsₘ_eq_containsKey h₂]
        rw [containsKey_eq_contains_map_fst]
  · rw [eraseManyEntries_eq_eraseListₘ]
    apply Perm.trans (toListModel_eraseListₘ h₁)
    · apply eraseList_perm_filter_not_contains
      · exact h₁.distinct

theorem diff_eq_diffₘ [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) :
    diff m₁ m₂ = diffₘ m₁ m₂ := by
  rw [diff, diffₘ]
  split
  · rw [filter_eq_filterₘ]
    congr
  · rw [eraseMany_eq_eraseListₘ_toListModel]
    rw [eraseManyEntries_eq_eraseListₘ]

theorem toListModel_diff [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Raw₀ α β}
    (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    Perm (toListModel (m₁.diff m₂).1.buckets)
     (List.filter (fun k => !List.contains ((toListModel m₂.1.buckets).map Sigma.fst) k.fst) (toListModel m₁.1.buckets)) := by
  rw [diff_eq_diffₘ]
  exact toListModel_diffₘ h₁ h₂

theorem wf_diff₀ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw α β} {h₁ : 0 < m₁.buckets.size} {h₂ : 0 < m₂.buckets.size} (h'₁ : m₁.WF) :
    (Raw₀.diff ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1.WF := by
  rw [diff]
  split
  · apply Raw.WF.filter₀ h'₁
  · exact wf_eraseMany₀ ‹_›

/-! # `insertManyIfNew` -/

theorem wfImp_insertManyIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] {m : Raw₀ α β} {l : ρ} (h : Raw.WFImp m.1) :
    Raw.WFImp (m.insertManyIfNew l).1.1 :=
  Raw.WF.out ((m.insertManyIfNew l).2 _ Raw.WF.insertIfNew₀ (.wf m.2 h))

theorem wf_insertManyIfNew₀ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] {m : Raw α β} {h : 0 < m.buckets.size} {l : ρ} (h' : m.WF) :
    (Raw₀.insertManyIfNew ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.insertManyIfNew ⟨m, h⟩ l).2 _ Raw.WF.insertIfNew₀ h'

theorem toListModel_insertManyIfNew_list [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × (β a))} (h : Raw.WFImp m.1) :
    Perm (toListModel (insertManyIfNew m l).1.1.buckets)
      (List.insertListIfNew (toListModel m.1.buckets) l) := by
  rw [insertManyIfNew_eq_insertListIfNewₘ]
  apply toListModel_insertListIfNewₘ
  exact h

/-! # `union` -/

theorem wf_union₀ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw α β} {h₁ : 0 < m₁.buckets.size} {h₂ : 0 < m₂.buckets.size} (h'₁ : m₁.WF)
    (h'₂ : m₂.WF) :
    (Raw₀.union ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1.WF := by
  rw [union]
  split
  · exact wf_insertManyIfNew₀ ‹_›
  · exact wf_insertMany₀ ‹_›


theorem toListModel_union [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] {m₁ m₂ : Raw₀ α β}
    (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    Perm (toListModel (m₁.union m₂).1.buckets)
      (List.insertList (toListModel m₁.1.buckets) (toListModel m₂.1.buckets)) := by
  rw [union_eq_unionₘ]
  exact toListModel_unionₘ h₁ h₂


/-! # `inter` -/

theorem wfImp_interSmallerFnₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m₁ : Raw₀ α β) (m₂ : Raw₀ α β)
    (hm₂ : Raw.WFImp m₂.1) (k : α) : Raw.WFImp (m₁.interSmallerFnₘ m₂ k).1 := by
  rw [interSmallerFnₘ]
  split
  · exact wfImp_insertₘ hm₂
  · exact hm₂

/-- Internal implementation detail of the hash map -/
def interSmallerₘ [BEq α] [Hashable α] (m₁ : Raw₀ α β) (m₂ : Raw α β) : Raw₀ α β :=
  m₂.fold (fun sofar k _ => interSmallerFnₘ m₁ sofar k) emptyWithCapacity

theorem interSmaller_eq_interSmallerₘ [BEq α] [Hashable α] (m₁ : Raw₀ α β) (m₂ : Raw α β) :
    m₁.interSmaller m₂ = m₁.interSmallerₘ m₂ := by
  rw [interSmaller, interSmallerₘ]
  simp only [interSmallerFn_eq_interSmallerFnₘ]

theorem foldl_perm_cong  [BEq α] {init₁ init₂ : List ((a : α) × β a)} {l : List ((a : α) × β a)}
    {f : List ((a : α) × β a) → ((a : α) × β a) → List ((a : α) × β a)} (h₁ : Perm init₁ init₂)
    (h₂ : ∀ h l₁ l₂, (w : DistinctKeys l₁) → Perm l₁ l₂ → Perm (f l₁ h) (f l₂ h) ∧ DistinctKeys (f l₁ h))
    (h₃ : DistinctKeys init₁)
     : Perm (List.foldl f init₁ l) (List.foldl f init₂ l) := by
  induction l generalizing init₁ init₂
  case nil =>
    simp only [foldl_nil, h₁]
  case cons h t ih =>
    simp only [foldl_cons]
    apply ih
    · exact (h₂ h init₁ init₂ h₃ h₁).1
    · exact (h₂ h init₁ init₂ h₃ h₁).2

theorem toListModel_interSmallerFnₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m sofar : Raw₀ α β)
    (l : List ((a : α) × β a))
    (hm : Raw.WFImp m.1) (hs : Raw.WFImp sofar.1) (k : α) (hml : toListModel sofar.1.buckets ~ l) :
    Perm (toListModel ((interSmallerFnₘ m sofar k).1.buckets))
      (List.interSmallerFn (toListModel m.1.buckets) l k) := by
  rw [interSmallerFnₘ, getEntry?ₘ_eq_getEntry? hm, List.interSmallerFn]
  split
  · simpa [*] using (toListModel_insertₘ hs).trans (List.insertEntry_of_perm hs.distinct hml)
  · simp [*]

theorem toListModel_interSmallerₘ [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α]
    (m₁ : Raw₀ α β) (m₂ : Raw α β) (hm₁ : Raw.WFImp m₁.1) :
    toListModel (m₁.interSmallerₘ m₂).1.buckets ~
      List.interSmaller (toListModel m₁.1.buckets) (toListModel m₂.buckets) := by
  rw [interSmallerₘ, Raw.fold_eq_foldl_toListModel, List.interSmaller]
  generalize toListModel m₂.buckets = l
  suffices ∀ m l', Raw.WFImp m.1 → toListModel m.1.buckets ~ l' → toListModel (foldl (fun a b => m₁.interSmallerFnₘ a b.fst) m l).val.buckets ~
      foldl (fun sofar kv => List.interSmallerFn (toListModel m₁.val.buckets) sofar kv.fst) l' l by
    simpa using this emptyWithCapacity [] wfImp_emptyWithCapacity (by simp)
  intro m l' hm hml'
  induction l generalizing m l' with
  | nil => simpa
  | cons ht tl ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih _ _ (wfImp_interSmallerFnₘ _ _ hm _) (toListModel_interSmallerFnₘ _ _ _ hm₁ hm _ hml')

theorem toListModel_inter [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] (m₁ m₂ : Raw₀ α β) (hm₁ : Raw.WFImp m₁.1) (hm₂ : Raw.WFImp m₂.1) :
    Perm (toListModel (m₁.inter m₂).1.buckets) ((toListModel m₁.1.buckets).filter fun p => containsKey p.1 (toListModel m₂.1.buckets) ) := by
  simp [inter]
  split
  · rw [filter_eq_filterₘ]
    simp only [contains_eq_containsKey hm₂]
    exact toListModel_filterₘ
  · rw [interSmaller_eq_interSmallerₘ]
    exact Perm.trans (toListModel_interSmallerₘ _ _ hm₁)
      (interSmaller_perm_filter _ _ hm₁.distinct)

/-! # `Const.insertListₘ` -/

theorem Const.toListModel_insertListₘ {β : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] {m : Raw₀ α (fun _ => β)} {l : List (α × β)} (h : Raw.WFImp m.1) :
    Perm (toListModel (Const.insertListₘ m l).1.buckets)
      (insertListConst (toListModel m.1.buckets) l) := by
  induction l generalizing m with
  | nil => simp [Const.insertListₘ, insertListConst, insertList]
  | cons hd tl ih =>
    simp only [Const.insertListₘ, insertListConst]
    apply Perm.trans (ih (wfImp_insert h))
    unfold insertListConst
    apply List.insertList_perm_of_perm_first (toListModel_insert h) (wfImp_insert h).distinct

/-! # `Const.insertMany` -/

theorem Const.toListModel_insertMany_list {β : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] {m : Raw₀ α (fun _ => β)} {l : List (α × β)} (h : Raw.WFImp m.1) :
    Perm (toListModel (Const.insertMany m l).1.1.buckets)
      (insertListConst (toListModel m.1.buckets) l) := by
  rw [Const.insertMany_eq_insertListₘ]
  apply toListModel_insertListₘ h

theorem Const.wfImp_insertMany {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {ρ : Type w} [ForIn Id ρ (α × β)] {m : Raw₀ α (fun _ => β)}
    {l : ρ} (h : Raw.WFImp m.1) : Raw.WFImp (Const.insertMany m l).1.1 :=
  Raw.WF.out ((Const.insertMany m l).2 _ Raw.WF.insert₀ (.wf m.2 h))

theorem Const.wf_insertMany₀ {β : Type v} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {ρ : Type w} [ForIn Id ρ (α × β)] {m : Raw α (fun _ => β)} {h : 0 < m.buckets.size}
    {l : ρ} (h' : m.WF) : (Const.insertMany ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.Const.insertMany ⟨m, h⟩ l).2 _ Raw.WF.insert₀ h'

/-! # `Const.insertListIfNewUnitₘ` -/

theorem Const.toListModel_insertListIfNewUnitₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => Unit)} {l : List α} (h : Raw.WFImp m.1) :
    Perm (toListModel (Const.insertListIfNewUnitₘ m l).1.buckets)
      (List.insertListIfNewUnit (toListModel m.1.buckets) l) := by
  induction l generalizing m with
  | nil => simp [insertListIfNewUnitₘ, List.insertListIfNewUnit]
  | cons hd tl ih =>
    simp only [insertListIfNewUnitₘ, insertListIfNewUnit]
    apply Perm.trans (ih (wfImp_insertIfNew h))
    apply List.insertListIfNewUnit_perm_of_perm_first (toListModel_insertIfNew h)
    apply (wfImp_insertIfNew h).distinct

/-! # `Const.insertManyIfNewUnit` -/

theorem Const.toListModel_insertManyIfNewUnit_list [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] {m : Raw₀ α (fun _ => Unit)} {l : List α} (h : Raw.WFImp m.1) :
    Perm (toListModel (Const.insertManyIfNewUnit m l).1.1.buckets)
      (List.insertListIfNewUnit (toListModel m.1.buckets) l) := by
  rw [Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  apply toListModel_insertListIfNewUnitₘ h

theorem Const.wfImp_insertManyIfNewUnit [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {ρ : Type w} [ForIn Id ρ α] {m : Raw₀ α (fun _ => Unit)} {l : ρ} (h : Raw.WFImp m.1) :
    Raw.WFImp (Const.insertManyIfNewUnit m l).1.1 :=
  Raw.WF.out ((Const.insertManyIfNewUnit m l).2 _ Raw.WF.insertIfNew₀ (.wf m.2 h))

theorem Const.wf_insertManyIfNewUnit₀ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {ρ : Type w} [ForIn Id ρ α] {m : Raw α (fun _ => Unit)} {h : 0 < m.buckets.size}
    {l : ρ} (h' : m.WF) : (Const.insertManyIfNewUnit ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.Const.insertManyIfNewUnit ⟨m, h⟩ l).2 _ Raw.WF.insertIfNew₀ h'

theorem beq_eq_beqModel [BEq α] [LawfulBEq α] [Hashable α] [∀ k, BEq (β k)] {m₁ m₂ : Raw₀ α β}  (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    beq m₁ m₂ = beqModel (toListModel m₁.1.buckets) (toListModel m₂.1.buckets) := by
  simp [beq, beqModel, Raw.size_eq_length h₁, Raw.size_eq_length h₂, Raw.all_eq_all_toListModel,
    get?_eq_getValueCast? h₂]

theorem Const.beq_eq_beqModel {β : Type v} [BEq α] [PartialEquivBEq α] [Hashable α] [LawfulHashable α] [BEq β] {m₁ m₂ : Raw₀ α (fun _ => β)} (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    beq m₁ m₂ = Const.beqModel (toListModel m₁.1.buckets) (toListModel m₂.1.buckets) := by
  simp [beq, Const.beqModel, Raw.size_eq_length h₁, Raw.size_eq_length h₂, Raw.all_eq_all_toListModel, get?_eq_getValue? h₂]

end Raw₀
