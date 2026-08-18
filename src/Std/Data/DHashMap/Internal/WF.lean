/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module
prelude
import all Std.Data.Internal.List.Associative
import all Std.Data.DHashMap.Raw
import all Std.Data.DHashMap.RawDef
import all Std.Data.DHashMap.Internal.AssocList.Basic
import all Std.Data.DHashMap.Internal.Defs
public import Std.Data.DHashMap.Internal.Model
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.Array.MapIdx
import Init.Data.List.Perm
import Init.Omega

public section

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

The proofs connect the flat linear-probing table to the existing list model and show that all
operations preserve `Raw.WFImp`.
-/

open Std.Internal.List Std.Internal
open List

set_option autoImplicit false
set_option pp.universes false

universe u v w w'
variable {α : Type u} {β : α → Type v}

namespace Std.DHashMap.Internal

@[simp] theorem toListModel_replicate_nil {c} :
    toListModel (Array.replicate c (AssocList.nil : AssocList α β)) = [] := by
  suffices ∀ d, (List.replicate d AssocList.nil).flatMap AssocList.toList = [] from this _
  intro d
  induction d <;> simp_all [List.replicate]

theorem cellEntry_eq_none_of_key_eq_none (key : NOption α) (value : NOption (NSigma β))
    (h : Raw.CellsMatch key value) (hk : key = .none) :
    Raw.CellsMatch.entry? key value h = none := by
  subst key
  rfl

theorem cellEntry_eq_none_of_value_eq_none (key : NOption α) (value : NOption (NSigma β))
    (h : Raw.CellsMatch key value) (hv : value = .none) :
    Raw.CellsMatch.entry? key value h = none := by
  subst value
  cases key <;> rfl

theorem entryAtInBounds_eq_none_of_key_eq_none (b : DHashMap.Raw α β) (i : Nat)
    (hi : i < b.keyArray.size) (hk : b.keyArray[i] = .none) :
    b.entryAtInBounds? i hi = none := by
  unfold DHashMap.Raw.entryAtInBounds?
  split <;> rename_i hv
  · simp [Raw.cellEntry?, hk]
  · rfl

theorem entryAtInBounds_eq_none_of_value_eq_none (b : DHashMap.Raw α β) (i : Nat)
    (hi : i < b.keyArray.size) (hiv : i < b.valueArray.size)
    (hv : b.valueArray[i]'hiv = .none) :
    b.entryAtInBounds? i hi = none := by
  rw [Raw.entryAtInBounds_eq_entryAtInBoundsImpl]
  unfold Raw.entryAtInBoundsImpl?
  exact cellEntry_eq_none_of_value_eq_none _ _ _ hv

theorem emptyWithCellCount_entryAt_eq_none {n : Nat} (h : 0 < n) (i : Nat) :
    (Raw₀.emptyWithCellCount n h : Raw₀ α β).1.entryAt? i = none := by
  unfold Raw.entryAt?
  by_cases hi : i < (Raw₀.emptyWithCellCount n h : Raw₀ α β).1.keyArray.size
  · rw [dite_eq_left hi]
    apply entryAtInBounds_eq_none_of_key_eq_none
    simp [Raw₀.emptyWithCellCount]
  · rw [dite_eq_right hi]

theorem toListModel_buckets_eq (b : Raw α β) :
    toListModel b.buckets = (b.entriesFrom 0).toList := by
  simp [toListModel, Raw.buckets]

@[simp] theorem entriesFrom_emptyWithCellCount {n : Nat} (h : 0 < n) (i : Nat) :
    (Raw₀.emptyWithCellCount n h : Raw₀ α β).1.entriesFrom i = .nil := by
  rw [Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · rw [entryAtInBounds_eq_none_of_key_eq_none]
    · apply entriesFrom_emptyWithCellCount
    · simp [Raw₀.emptyWithCellCount]
  · rfl
termination_by (Raw₀.emptyWithCellCount n h : Raw₀ α β).1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem entriesFrom_eq_nil_of_values_none (b : Raw α β)
    (hvalues : ∀ (i : Nat) (hi : i < b.valueArray.size), b.valueArray[i] = .none)
    (i : Nat) : b.entriesFrom i = .nil := by
  rw [Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · by_cases hiv : i < b.valueArray.size
    · rw [entryAtInBounds_eq_none_of_value_eq_none b i hi hiv (hvalues i hiv)]
      exact entriesFrom_eq_nil_of_values_none b hvalues (i + 1)
    · rw [Raw.entryAtInBounds?]
      simp only [dite_eq_right hiv]
      exact entriesFrom_eq_nil_of_values_none b hvalues (i + 1)
  · rfl
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

@[simp] theorem emptyWithCellCount_toListModel {n : Nat} (h : 0 < n) :
    toListModel (Raw₀.emptyWithCellCount n h : Raw₀ α β).1.buckets = [] := by
  rw [toListModel_buckets_eq, entriesFrom_emptyWithCellCount]
  simp

@[simp] theorem buckets_emptyWithCellCount {n : Nat} (hn : 0 < n)
    {i : Nat} {hi : i < (Raw₀.emptyWithCellCount n hn : Raw₀ α β).1.buckets.size} :
    (Raw₀.emptyWithCellCount n hn : Raw₀ α β).1.buckets[i] = .nil := by
  have hiz : i = 0 := by
    simp [Raw.buckets] at hi
    omega
  subst i
  simp [Raw.buckets]

@[simp] theorem scanFrom_emptyWithCellCount [BEq α] {n : Nat} (hn : 0 < n)
    (a : α) (i : Nat) :
    (Raw₀.emptyWithCellCount n hn : Raw₀ α β).scanFrom a i = .absent := by
  rw [Raw₀.scanFrom.eq_def]
  split <;> rename_i hi
  · rw [entryAtInBounds_eq_none_of_key_eq_none]
    · exact scanFrom_emptyWithCellCount hn a (i + 1)
    · simp [Raw₀.emptyWithCellCount]
  · rfl
termination_by (Raw₀.emptyWithCellCount n hn : Raw₀ α β).1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

@[simp] theorem scan_emptyWithCellCount [BEq α] [Hashable α] {n : Nat} (hn : 0 < n)
    (a : α) : (Raw₀.emptyWithCellCount n hn : Raw₀ α β).scan a = .absent := by
  cases n with
  | zero => omega
  | succ n =>
    simp [Raw₀.scan, Raw₀.probe, Raw₀.probeFrom, Raw₀.probeFromAux,
      Raw₀.emptyWithCellCount]

@[simp] theorem scan_emptyWithCapacity [BEq α] [Hashable α] (c : Nat) (a : α) :
    (Raw₀.emptyWithCapacity c : Raw₀ α β).scan a = .absent := by
  simp [Raw₀.emptyWithCapacity]

@[simp] theorem get?_emptyWithCellCount [BEq α] [Hashable α] [LawfulBEq α]
    (n : Nat) (hn : 0 < n) (a : α) :
    (Raw₀.emptyWithCellCount n hn : Raw₀ α β).get? a = none := by
  simp [Raw₀.get?]

@[simp] theorem constGet?_emptyWithCellCount {γ : Type w} [BEq α] [Hashable α]
    (n : Nat) (hn : 0 < n) (a : α) :
    Raw₀.Const.get? (Raw₀.emptyWithCellCount n hn : Raw₀ α (fun _ => γ)) a = none := by
  simp [Raw₀.Const.get?]

@[simp] theorem getKey?_emptyWithCellCount [BEq α] [Hashable α]
    (n : Nat) (hn : 0 < n) (a : α) :
    (Raw₀.emptyWithCellCount n hn : Raw₀ α β).getKey? a = none := by
  simp [Raw₀.getKey?]

theorem foldMFrom_eq_def {γ : Type w} {m : Type w → Type w'} [Monad m]
    (f : γ → (a : α) → β a → m γ) (b : Raw α β) (acc : γ) (i : Nat) :
    Raw.foldMFrom f b acc i =
      if h : i < b.keyArray.size then
        match b.entryAtInBounds? i h with
        | .none => Raw.foldMFrom f b acc (i + 1)
        | .some ⟨k, v⟩ => f acc k v >>= fun acc => Raw.foldMFrom f b acc (i + 1)
      else
        pure acc := by
  rw [Raw.foldMFrom.eq_def]
  split <;> rename_i h
  · cases b.entryAtInBounds? i h <;> rfl
  · rfl

theorem foldMFrom_eq_foldlM {γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    (f : γ → (a : α) → β a → m γ) (b : Raw α β) (acc : γ) (i : Nat) :
    Raw.foldMFrom f b acc i = (b.entriesFrom i).foldlM f acc := by
  rw [foldMFrom_eq_def, Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · generalize b.entryAtInBounds? i hi = entry
    cases entry with
    | none =>
      rw [foldMFrom_eq_foldlM]
    | some p =>
      rcases p with ⟨k, v⟩
      change (f acc k v >>= fun acc' => Raw.foldMFrom f b acc' (i + 1)) =
        (f acc k v >>= fun acc' => AssocList.foldlM f acc' (b.entriesFrom (i + 1)))
      congr 1
      funext acc'
      exact foldMFrom_eq_foldlM f b acc' (i + 1)
  · change pure acc = pure acc
    rfl
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem cellEntry_eq_some_of_cells_eq_some (key : NOption α) (value : NOption (NSigma β))
    (h : Raw.CellsMatch key value) (k : α) (v : β k)
    (hk : key = .some k) (hv : value = .some (.mk k v)) :
    Raw.CellsMatch.entry? key value h = some ⟨k, v⟩ := by
  subst key
  subst value
  change Option.some (Sigma.mk k (h ▸ (NSigma.mk k v).snd)) = Option.some (Sigma.mk k v)
  have hh : h = NSigma.fst_mk k v := Subsingleton.elim _ _
  rw [hh]
  unfold NSigma.mk
  congr 2
  apply eq_of_heq
  exact (eqRec_heq _ _).trans (eqRec_heq _ _)

theorem rawCellEntry_eq_some (k : α) (v : β k) :
    Raw.cellEntry? (.some k) (.some (.mk k v)) = some ⟨k, v⟩ := by
  unfold Raw.cellEntry?
  apply congrArg Option.some
  apply Sigma.ext
  · exact NSigma.fst_mk k v
  · unfold NSigma.mk
    exact eqRec_heq _ _

theorem keyArray_eq_some_of_entryAtInBounds_eq_some (b : Raw α β) (i : Nat)
    (hi : i < b.keyArray.size) (hkv : Raw.KeysValues b.keyArray b.valueArray)
    (k : α) (v : β k) (hentry : b.entryAtInBounds? i hi = some ⟨k, v⟩) :
    b.keyArray[i] = .some k := by
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  have hcell := hkv.2 i hi hiv
  unfold Raw.entryAtInBounds? at hentry
  rw [dite_eq_left hiv] at hentry
  cases hk : b.keyArray[i] with
  | none => simp [Raw.cellEntry?, hk] at hentry
  | some key =>
    cases hv : b.valueArray[i] with
    | none => simp [Raw.cellEntry?, hk, hv] at hentry
    | some value =>
      rw [hk, hv] at hentry
      change (some (Sigma.mk value.fst value.snd) : Option ((a : α) × β a)) =
        some (Sigma.mk k v) at hentry
      have hpair : Sigma.mk value.fst value.snd = Sigma.mk k v := by
        exact Option.some.inj hentry
      have hfst : value.fst = k := congrArg Sigma.fst hpair
      have hmatch : value.fst = key := by
        simpa [Raw.CellsMatch, hk, hv] using hcell
      simp [hmatch.symm.trans hfst]

theorem keysValues_setEntry (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (k : α) (v : β k) :
    Raw.KeysValues (b.setEntry size i hi k v).keyArray
      (b.setEntry size i hi k v).valueArray := by
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  have hset := Raw.keysValues_set hkv i hi hiv (.some k) (.some (.mk k v))
    (by simp [Raw.CellsMatch])
  simpa [Raw.setEntry, Raw.setCell, Array.setIfInBounds_def, hiv] using hset

theorem keyArray_setEntry_ne_none (b : Raw α β) (size i : Nat)
    (hi : i < b.keyArray.size) (k : α) (v : β k) (j : Nat)
    (hj : j < b.keyArray.size)
    (hkey : b.keyArray[j] ≠ .none) :
    (b.setEntry size i hi k v).keyArray[j]'(by simpa [Raw.setEntry, Raw.setCell] using hj) ≠
      .none := by
  by_cases hji : j = i
  · subst j
    simp [Raw.setEntry, Raw.setCell]
  · simp only [Raw.setEntry, Raw.setCell]
    rw [Array.getElem_set_ne hi hj (Ne.symm hji)]
    exact hkey

theorem keysValues_clearCell (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) :
    Raw.KeysValues (b.clearCell size i hi).keyArray (b.clearCell size i hi).valueArray := by
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  have hcell : Raw.CellsMatch b.keyArray[i] (NOption.none : NOption (NSigma β)) := by
    cases hkey : b.keyArray[i] <;> simp [Raw.CellsMatch]
  have hset := Raw.keysValues_set hkv i hi hiv b.keyArray[i] .none hcell
  simpa [Raw.clearCell, Raw.setCell, Array.setIfInBounds_def, hiv] using hset

theorem entryAtInBounds_setEntry_self (b : Raw α β) (size i : Nat)
    (hi : i < b.keyArray.size) (hkv : Raw.KeysValues b.keyArray b.valueArray)
    (k : α) (v : β k) :
    (b.setEntry size i hi k v).entryAtInBounds? i (by simpa [Raw.setEntry, Raw.setCell]) =
      some ⟨k, v⟩ := by
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  unfold Raw.entryAtInBounds?
  split <;> rename_i hivNew
  · simpa [Raw.setEntry, Raw.setCell] using rawCellEntry_eq_some k v
  · have : i < (b.setEntry size i hi k v).valueArray.size := by
      simpa [Raw.setEntry, Raw.setCell] using hiv
    contradiction

theorem entryAtInBounds_setEntry_ne (b : Raw α β) (size i j : Nat) (k : α) (v : β k)
    (hi : i < b.keyArray.size) (hj : j < (b.setEntry size i hi k v).keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (hne : j ≠ i) :
    (b.setEntry size i hi k v).entryAtInBounds? j hj =
      b.entryAtInBounds? j (by simpa [Raw.setEntry, Raw.setCell] using hj) := by
  have hj' : j < b.keyArray.size := by simpa [Raw.setEntry, Raw.setCell] using hj
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  have hjv : j < b.valueArray.size := by simpa [hkv.1] using hj'
  unfold Raw.entryAtInBounds?
  split <;> rename_i hjvNew
  · simp only [Raw.setEntry, Raw.setCell]
    rw [Array.getElem_set_ne hi hj' (Ne.symm hne)]
    rw [Array.getElem_setIfInBounds_ne hjv (Ne.symm hne)]
  · have : j < (b.setEntry size i hi k v).valueArray.size := by
      simpa [Raw.setEntry, Raw.setCell] using hjv
    contradiction

theorem entryAtInBounds_clearCell_self (b : Raw α β) (size i : Nat)
    (hi : i < b.keyArray.size) (hkv : Raw.KeysValues b.keyArray b.valueArray) :
    (b.clearCell size i hi).entryAtInBounds? i (by simpa [Raw.clearCell]) =
      none := by
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  exact entryAtInBounds_eq_none_of_value_eq_none (b.clearCell size i hi) i
    (by simpa [Raw.clearCell] using hi)
    (by simpa [Raw.clearCell] using hiv)
    (by simp [Raw.clearCell])

theorem entryAtInBounds_clearCell_ne (b : Raw α β) (size i j : Nat)
    (hi : i < b.keyArray.size) (hj : j < (b.clearCell size i hi).keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (hne : j ≠ i) :
    (b.clearCell size i hi).entryAtInBounds? j hj =
      b.entryAtInBounds? j (by simpa [Raw.clearCell] using hj) := by
  have hj' : j < b.keyArray.size := by simpa [Raw.clearCell] using hj
  have hiv : i < b.valueArray.size := by simpa [hkv.1] using hi
  have hjv : j < b.valueArray.size := by simpa [hkv.1] using hj'
  unfold Raw.entryAtInBounds?
  split <;> rename_i hjvNew
  · simp only [Raw.clearCell]
    rw [Array.getElem_setIfInBounds_ne hjv (Ne.symm hne)]
    rfl
  · have : j < (b.clearCell size i hi).valueArray.size := by
      simpa [Raw.clearCell] using hjv
    contradiction

theorem entryAtInBounds_congr {b c : Raw α β} (hbc : b = c) (i : Nat)
    (hb : i < b.keyArray.size) (hc : i < c.keyArray.size) :
    b.entryAtInBounds? i hb = c.entryAtInBounds? i hc := by
  subst c
  rfl

theorem entriesFrom_setEntry_of_lt (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (k : α) (v : β k)
    (j : Nat) (hij : i < j) :
    (b.setEntry size i hi k v).entriesFrom j = b.entriesFrom j := by
  suffices ∀ d j, b.keyArray.size - j = d → i < j →
      (b.setEntry size i hi k v).entriesFrom j = b.entriesFrom j from
    this (b.keyArray.size - j) j rfl hij
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro j hd hij
    rw [Raw.entriesFrom.eq_def (b := b.setEntry size i hi k v) (i := j)]
    rw [Raw.entriesFrom.eq_def (b := b) (i := j)]
    have hs : (b.setEntry size i hi k v).keyArray.size = b.keyArray.size := by
      simp [Raw.setEntry, Raw.setCell]
    split <;> rename_i hj
    · have hj' : j < b.keyArray.size := by simpa [hs] using hj
      rw [entryAtInBounds_setEntry_ne (hkv := hkv) (hne := by omega)]
      rw [dite_eq_left hj']
      generalize b.entryAtInBounds? j hj' = entry
      cases entry with
      | none =>
        apply ih (b.keyArray.size - (j + 1)) (by omega) (j + 1) rfl
        omega
      | some p =>
        rcases p with ⟨k', v'⟩
        change AssocList.cons k' v' ((b.setEntry size i hi k v).entriesFrom (j + 1)) =
          AssocList.cons k' v' (b.entriesFrom (j + 1))
        apply congrArg
        apply ih (b.keyArray.size - (j + 1)) (by omega) (j + 1) rfl
        omega
    · have hj' : ¬j < b.keyArray.size := by simpa [hs] using hj
      rw [dite_eq_right hj']

theorem entriesFrom_setEntry_split (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (k : α) (v : β k)
    (j : Nat) (hji : j ≤ i) :
    ∃ pre post : List ((a : α) × β a),
      (b.entriesFrom j).toList =
        pre ++ (b.entryAtInBounds? i hi).toList ++ post ∧
      ((b.setEntry size i hi k v).entriesFrom j).toList =
        pre ++ [⟨k, v⟩] ++ post := by
  have hj : j < b.keyArray.size := Nat.lt_of_le_of_lt hji hi
  have hjnew : j < (b.setEntry size i hi k v).keyArray.size := by
    simpa [Raw.setEntry, Raw.setCell] using hj
  rw [Raw.entriesFrom.eq_def (b := b) (i := j), dite_eq_left hj]
  rw [Raw.entriesFrom.eq_def (b := b.setEntry size i hi k v) (i := j),
    dite_eq_left hjnew]
  by_cases hji' : j = i
  · subst j
    rw [entryAtInBounds_setEntry_self (hkv := hkv)]
    have ht := entriesFrom_setEntry_of_lt b size i hi hkv k v (i + 1) (by omega)
    cases he : b.entryAtInBounds? i hi with
    | none =>
      refine ⟨[], (b.entriesFrom (i + 1)).toList, ?_, ?_⟩
      · simp
      · simp [ht]
    | some p =>
      rcases p with ⟨k', v'⟩
      refine ⟨[], (b.entriesFrom (i + 1)).toList, ?_, ?_⟩
      · simp
      · simp [ht]
  · have hjiLt : j < i := Nat.lt_of_le_of_ne hji hji'
    rw [entryAtInBounds_setEntry_ne (hkv := hkv) (hne := by omega)]
    obtain ⟨pre, post, hold, hnew⟩ :=
      entriesFrom_setEntry_split b size i hi hkv k v (j + 1) (by omega)
    cases he : b.entryAtInBounds? j hj with
    | none =>
      refine ⟨pre, post, ?_, ?_⟩
      · simpa using hold
      · simpa using hnew
    | some p =>
      rcases p with ⟨k', v'⟩
      refine ⟨⟨k', v'⟩ :: pre, post, ?_, ?_⟩
      · simpa [List.cons_append] using congrArg (List.cons ⟨k', v'⟩) hold
      · simpa [List.cons_append] using congrArg (List.cons ⟨k', v'⟩) hnew
termination_by i + 1 - j
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ (by omega)

theorem entriesFrom_clearCell_of_lt (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (j : Nat) (hij : i < j) :
    (b.clearCell size i hi).entriesFrom j = b.entriesFrom j := by
  rw [Raw.entriesFrom.eq_def (b := b.clearCell size i hi) (i := j)]
  rw [Raw.entriesFrom.eq_def (b := b) (i := j)]
  have hs : (b.clearCell size i hi).keyArray.size = b.keyArray.size := by
    simp [Raw.clearCell]
  split <;> rename_i hj
  · have hj' : j < b.keyArray.size := by simpa [hs] using hj
    rw [entryAtInBounds_clearCell_ne (hkv := hkv) (hne := by omega)]
    rw [dite_eq_left hj']
    cases he : b.entryAtInBounds? j hj' with
    | none =>
      simp only
      apply entriesFrom_clearCell_of_lt
      · exact hkv
      omega
    | some p =>
      rcases p with ⟨k', v'⟩
      simp only
      apply congrArg
      apply entriesFrom_clearCell_of_lt
      · exact hkv
      omega
  · have hj' : ¬j < b.keyArray.size := by simpa [hs] using hj
    rw [dite_eq_right hj']
termination_by b.keyArray.size - j
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem entriesFrom_clearCell_split (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray) (j : Nat) (hji : j ≤ i) :
    ∃ pre post : List ((a : α) × β a),
      (b.entriesFrom j).toList =
        pre ++ (b.entryAtInBounds? i hi).toList ++ post ∧
      ((b.clearCell size i hi).entriesFrom j).toList = pre ++ post := by
  have hj : j < b.keyArray.size := Nat.lt_of_le_of_lt hji hi
  have hjnew : j < (b.clearCell size i hi).keyArray.size := by
    simpa [Raw.clearCell, Raw.setCell] using hj
  rw [Raw.entriesFrom.eq_def (b := b) (i := j), dite_eq_left hj]
  rw [Raw.entriesFrom.eq_def (b := b.clearCell size i hi) (i := j),
    dite_eq_left hjnew]
  by_cases hji' : j = i
  · subst j
    rw [entryAtInBounds_clearCell_self (hkv := hkv)]
    have ht := entriesFrom_clearCell_of_lt b size i hi hkv (i + 1) (by omega)
    cases he : b.entryAtInBounds? i hi with
    | none =>
      refine ⟨[], (b.entriesFrom (i + 1)).toList, ?_, ?_⟩
      · simp
      · simp [ht]
    | some p =>
      rcases p with ⟨k', v'⟩
      refine ⟨[], (b.entriesFrom (i + 1)).toList, ?_, ?_⟩
      · simp
      · simp [ht]
  · have hjiLt : j < i := Nat.lt_of_le_of_ne hji hji'
    rw [entryAtInBounds_clearCell_ne (hkv := hkv) (hne := by omega)]
    obtain ⟨pre, post, hold, hnew⟩ :=
      entriesFrom_clearCell_split b size i hi hkv (j + 1) (by omega)
    cases he : b.entryAtInBounds? j hj with
    | none =>
      refine ⟨pre, post, ?_, ?_⟩
      · simpa using hold
      · simpa using hnew
    | some p =>
      rcases p with ⟨k', v'⟩
      refine ⟨⟨k', v'⟩ :: pre, post, ?_, ?_⟩
      · simpa [List.cons_append] using congrArg (List.cons ⟨k', v'⟩) hold
      · simpa [List.cons_append] using congrArg (List.cons ⟨k', v'⟩) hnew
termination_by i + 1 - j
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ (by omega)

def scanResultEntry? [BEq α] {query : α} {n : Nat} : Raw₀.ScanResult β query n →
    Option ((a : α) × β a)
  | .found _ k v _ => some ⟨k, v⟩
  | .absent => none

def scanResultValueCast? [BEq α] [LawfulBEq α] (query : α) {n : Nat} :
    Raw₀.ScanResult β query n → Option (β query)
  | .found _ _k v h => some (cast (congrArg β (eq_of_beq h)) v)
  | .absent => none

theorem scanFrom_entry_eq_getEntry? [BEq α] (m : Raw₀ α β) (query : α) (i : Nat) :
    scanResultEntry? (m.scanFrom query i) =
      List.getEntry? query (m.1.entriesFrom i).toList := by
  rw [Raw₀.scanFrom.eq_def, Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · cases he : m.1.entryAtInBounds? i hi with
    | none =>
      simp only
      apply scanFrom_entry_eq_getEntry?
    | some p =>
      rcases p with ⟨k, v⟩
      change scanResultEntry?
          (if h : k == query then .found ⟨i, hi⟩ k v h else m.scanFrom query (i + 1)) =
        if k == query then some ⟨k, v⟩
        else List.getEntry? query (m.1.entriesFrom (i + 1)).toList
      by_cases hk : (k == query) = true
      · rw [dite_eq_left hk, ite_eq_left hk]
        rfl
      · rw [dite_eq_right hk, ite_eq_right hk]
        exact scanFrom_entry_eq_getEntry? m query (i + 1)
  · change none = none
    rfl
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem scanFrom_valueCast_eq_getValueCast? [BEq α] [LawfulBEq α]
    (m : Raw₀ α β) (query : α) (i : Nat) :
    scanResultValueCast? query (m.scanFrom query i) =
      List.getValueCast? query (m.1.entriesFrom i).toList := by
  rw [Raw₀.scanFrom.eq_def, Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · cases he : m.1.entryAtInBounds? i hi with
    | none =>
      simp only
      apply scanFrom_valueCast_eq_getValueCast?
    | some p =>
      rcases p with ⟨k, v⟩
      change scanResultValueCast? query
          (if h : k == query then .found ⟨i, hi⟩ k v h else m.scanFrom query (i + 1)) =
        if h : k == query then some (cast (congrArg β (eq_of_beq h)) v)
        else List.getValueCast? query (m.1.entriesFrom (i + 1)).toList
      by_cases hk : (k == query) = true
      · rw [dite_eq_left hk, dite_eq_left hk]
        rfl
      · rw [dite_eq_right hk, dite_eq_right hk]
        exact scanFrom_valueCast_eq_getValueCast? m query (i + 1)
  · change none = none
    rfl
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem scanFrom_found_cell [BEq α] (m : Raw₀ α β) (query : α) (i : Nat)
    (index : Fin m.1.keyArray.size) (k : α) (v : β k) (hmatch : k == query)
    (hscan : m.scanFrom query i = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  rw [Raw₀.scanFrom.eq_def] at hscan
  split at hscan <;> rename_i hi
  · cases he : m.1.entryAtInBounds? i hi with
    | none =>
      simp only [he] at hscan
      exact scanFrom_found_cell m query (i + 1) index k v hmatch hscan
    | some p =>
      rcases p with ⟨k', v'⟩
      simp only [he] at hscan
      split at hscan
      · cases hscan
        exact he
      · exact scanFrom_found_cell m query (i + 1) index k v hmatch hscan
  · contradiction
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem Raw₀.ProbePath.mono {keys keys' : Array (NOption α)}
    (hsize : keys'.size = keys.size)
    (hmono : ∀ (i : Nat) (hi : i < keys.size) (hi' : i < keys'.size),
      keys[i] ≠ .none → keys'[i] ≠ .none)
    {fuel start target : Nat} (path : Raw₀.ProbePath keys fuel start target) :
    Raw₀.ProbePath keys' fuel start target := by
  induction path with
  | here fuel i hi =>
    exact .here fuel i (by omega)
  | next hi hkey path ih =>
    refine Raw₀.ProbePath.next (i := _) (hi := by omega)
      (hmono _ hi (by omega) hkey) ?_
    simpa [Raw₀.nextIndexNat, hsize] using ih

private def probeDistance (n i target : Nat) : Nat :=
  if i ≤ target then target - i else n - i + target

private theorem probeDistance_lt {n i target : Nat} (hi : i < n) (htarget : target < n) :
    probeDistance n i target < n := by
  unfold probeDistance
  split <;> omega

private theorem probeDistance_next {n i target : Nat} (hi : i < n) (htarget : target < n)
    (hne : i ≠ target) :
    probeDistance n (Raw₀.nextIndexNat n i) target + 1 = probeDistance n i target := by
  unfold probeDistance Raw₀.nextIndexNat
  split <;> split <;> split <;> omega

private theorem probeFromAux_full_path [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size)) (fuel i : Nat)
    (hi : i < m.1.keyArray.size)
    (hfull : m.probeFromAux query firstEmpty fuel i hi = .full)
    (target : Nat) (htarget : target < m.1.keyArray.size)
    (hdistance : probeDistance m.1.keyArray.size i target < fuel) :
    Raw₀.ProbePath m.1.keyArray fuel i target := by
  induction fuel generalizing firstEmpty i with
  | zero => omega
  | succ fuel ih =>
    by_cases hit : i = target
    · subst i
      exact .here fuel target hi
    · have hdistance' :
          probeDistance m.1.keyArray.size (Raw₀.nextIndexNat m.1.keyArray.size i) target <
            fuel := by
        have hstep := probeDistance_next hi htarget hit
        omega
      rw [Raw₀.probeFromAux.eq_def] at hfull
      cases hkey : m.1.keyArray[i] with
      | none => cases firstEmpty <;> simp_all
      | some key =>
        have hkey' : m.1.keyArray[i] ≠ .none := by simp [hkey]
        have hdistanceNext :
            probeDistance m.1.keyArray.size (Raw₀.nextIndex m.2 ⟨i, hi⟩).1 target < fuel := by
          simpa only [Raw₀.nextIndex_val] using hdistance'
        cases hentry : m.1.entryAtInBounds? i hi with
        | none =>
          simp only [hkey, hentry] at hfull
          refine .next hi hkey' ?_
          simpa only [Raw₀.nextIndex_val] using ih _ _ _ hfull hdistanceNext
        | some p =>
          rcases p with ⟨k, v⟩
          simp only [hkey, hentry] at hfull
          split at hfull
          · contradiction
          · refine .next hi hkey' ?_
            simpa only [Raw₀.nextIndex_val] using ih _ _ _ hfull hdistanceNext

theorem probe_full_path [BEq α] [Hashable α] (m : Raw₀ α β) (query : α)
    (hfull : m.probe query = .full) (target : Nat) (htarget : target < m.1.keyArray.size) :
    Raw₀.ProbePath m.1.keyArray m.1.keyArray.size
      (Raw₀.probeStart m.1.keyArray.size (hash query)) target := by
  unfold Raw₀.probe Raw₀.probeFrom at hfull
  have hp := probeFromAux_full_path m query none _ _ _ hfull target htarget
    (probeDistance_lt (mkIdx m.1.keyArray.size m.2 (hash query)).2 htarget)
  simpa [Raw₀.probeStart, m.2] using hp

theorem reachable_setEntry [BEq α] [Hashable α] [EquivBEq α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (size i : Nat) (hi : i < m.1.keyArray.size)
    (a : α) (b : β a)
    (hnew : ∀ (query : α), a == query →
      Raw₀.ProbePath m.1.keyArray m.1.keyArray.size
        (Raw₀.probeStart m.1.keyArray.size (hash query)) i)
    (j : Nat) (hj : j < (m.1.setEntry size i hi a b).keyArray.size)
    (k : α) (hkey : (m.1.setEntry size i hi a b).keyArray[j] = .some k)
    (query : α) (hmatch : k == query) :
    Raw₀.ProbePath (m.1.setEntry size i hi a b).keyArray
      (m.1.setEntry size i hi a b).keyArray.size
      (Raw₀.probeStart (m.1.setEntry size i hi a b).keyArray.size (hash query)) j := by
  have hjOld : j < m.1.keyArray.size := by
    simpa [Raw.setEntry, Raw.setCell] using hj
  have hsize : (m.1.setEntry size i hi a b).keyArray.size = m.1.keyArray.size := by
    simp [Raw.setEntry, Raw.setCell]
  have hmono : ∀ (r : Nat) (hr : r < m.1.keyArray.size)
      (hr' : r < (m.1.setEntry size i hi a b).keyArray.size),
      m.1.keyArray[r] ≠ .none →
        (m.1.setEntry size i hi a b).keyArray[r] ≠ .none := by
    intro r hr _ hrkey
    exact keyArray_setEntry_ne_none m.1 size i hi a b r hr hrkey
  by_cases hji : j = i
  · subst j
    have hk : k = a := by
      simpa [Raw.setEntry, Raw.setCell] using hkey.symm
    subst k
    have hp := (hnew query hmatch).mono hsize hmono
    simpa [Raw.setEntry, Raw.setCell, hsize] using hp
  · have hkeyOld : m.1.keyArray[j] = .some k := by
      simp only [Raw.setEntry, Raw.setCell] at hkey
      rw [Array.getElem_set_ne hi hjOld (Ne.symm hji)] at hkey
      exact hkey
    have hp := (h.reachable j hjOld k hkeyOld query hmatch).mono hsize hmono
    simpa [Raw.setEntry, Raw.setCell, hsize] using hp

theorem probeFromAux_empty_path_or_first [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size)) (fuel i : Nat)
    (hi : i < m.1.keyArray.size) {index : Fin m.1.keyArray.size}
    (h : m.probeFromAux query firstEmpty fuel i hi = .empty index) :
    firstEmpty = some index ∨
      Raw₀.ProbePath m.1.keyArray fuel i index.1 := by
  induction fuel generalizing firstEmpty i with
  | zero =>
    simp only [Raw₀.probeFromAux] at h
    cases hf : firstEmpty with
    | none => simp [hf] at h
    | some first =>
      simp only [hf] at h
      cases h
      exact .inl rfl
  | succ fuel ih =>
    rw [Raw₀.probeFromAux.eq_def] at h
    cases hk : m.1.keyArray[i] with
    | none =>
      simp only [hk] at h
      cases hf : firstEmpty with
      | none =>
        simp only [hf] at h
        cases h
        exact .inr (.here fuel i hi)
      | some first =>
        simp only [hf] at h
        cases h
        exact .inl rfl
    | some key =>
      simp only [hk] at h
      have hkey : m.1.keyArray[i] ≠ .none := by simp [hk]
      cases he : m.1.entryAtInBounds? i hi with
      | none =>
        simp only [he] at h
        cases hf : firstEmpty with
        | none =>
          simp only [hf] at h
          rcases ih (some ⟨i, hi⟩) _ _ h with hfirst | hpath
          · right
            have hindex : (⟨i, hi⟩ : Fin m.1.keyArray.size) = index :=
              Option.some.inj hfirst
            cases hindex
            exact .here fuel i hi
          · right
            exact .next hi hkey (by simpa only [Raw₀.nextIndex_val] using hpath)
        | some first =>
          simp only [hf] at h
          rcases ih (some first) _ _ h with hfirst | hpath
          · left
            exact hfirst
          · right
            exact .next hi hkey (by simpa only [Raw₀.nextIndex_val] using hpath)
      | some p =>
        rcases p with ⟨k, v⟩
        simp only [he] at h
        split at h
        · contradiction
        · rcases ih firstEmpty _ _ h with hfirst | hpath
          · exact .inl hfirst
          · exact .inr (.next hi hkey (by simpa only [Raw₀.nextIndex_val] using hpath))

theorem probe_empty_path [BEq α] [Hashable α] (m : Raw₀ α β) (query : α)
    {index : Fin m.1.keyArray.size} (h : m.probe query = .empty index) :
    Raw₀.ProbePath m.1.keyArray m.1.keyArray.size
      (Raw₀.probeStart m.1.keyArray.size (hash query)) index.1 := by
  unfold Raw₀.probe at h
  simpa [Raw₀.probeStart, m.2] using
    (probeFromAux_empty_path_or_first m query none _ _ _ h).resolve_left (by simp)

theorem probeFromAux_empty_cell [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size))
    (hfirst : ∀ index, firstEmpty = some index →
      m.1.entryAtInBounds? index.1 index.2 = none)
    (fuel i : Nat) (hi : i < m.1.keyArray.size) {index : Fin m.1.keyArray.size}
    (h : m.probeFromAux query firstEmpty fuel i hi = .empty index) :
    m.1.entryAtInBounds? index.1 index.2 = none := by
  induction fuel generalizing firstEmpty i with
  | zero =>
    simp only [Raw₀.probeFromAux] at h
    cases hf : firstEmpty with
    | none => simp [hf] at h
    | some first =>
      simp only [hf] at h
      cases h
      exact hfirst _ hf
  | succ fuel ih =>
    rw [Raw₀.probeFromAux.eq_def] at h
    cases hk : m.1.keyArray[i] with
    | none =>
      simp only [hk] at h
      cases hf : firstEmpty with
      | none =>
        simp only [hf] at h
        cases h
        exact entryAtInBounds_eq_none_of_key_eq_none m.1 i hi hk
      | some first =>
        simp only [hf] at h
        cases h
        exact hfirst _ hf
    | some key =>
      simp only [hk] at h
      cases he : m.1.entryAtInBounds? i hi with
      | none =>
        simp only [he] at h
        cases hf : firstEmpty with
        | none =>
          simp only [hf] at h
          exact ih (some ⟨i, hi⟩) (fun first hfirst' => by
            cases hfirst'
            exact he) _ _ h
        | some first =>
          simp only [hf] at h
          exact ih (some first) (fun current hcurrent => by
            cases hcurrent
            exact hfirst first hf) _ _ h
      | some p =>
        rcases p with ⟨k, v⟩
        simp only [he] at h
        split at h
        · contradiction
        · exact ih firstEmpty hfirst _ _ h

theorem probeFrom_empty_cell [BEq α] (m : Raw₀ α β) (query : α) (fuel i : Nat)
    (hi : i < m.1.keyArray.size) {index : Fin m.1.keyArray.size}
    (h : m.probeFrom query fuel i hi = .empty index) :
    m.1.entryAtInBounds? index.1 index.2 = none := by
  exact probeFromAux_empty_cell m query none (by simp) fuel i hi h

theorem probeFromAux_found_cell [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size)) (fuel i : Nat)
    (hi : i < m.1.keyArray.size) (index : Fin m.1.keyArray.size)
    (k : α) (v : β k) (hmatch : k == query)
    (h : m.probeFromAux query firstEmpty fuel i hi = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  induction fuel generalizing firstEmpty i with
  | zero =>
    simp only [Raw₀.probeFromAux] at h
    cases firstEmpty <;> contradiction
  | succ fuel ih =>
    rw [Raw₀.probeFromAux.eq_def] at h
    cases hk : m.1.keyArray[i] with
    | none =>
      simp only [hk] at h
      cases firstEmpty <;> contradiction
    | some key =>
      simp only [hk] at h
      cases he : m.1.entryAtInBounds? i hi with
      | none =>
        simp only [he] at h
        cases hf : firstEmpty with
        | none =>
          simp only [hf] at h
          exact ih (some ⟨i, hi⟩) _ _ h
        | some first =>
          simp only [hf] at h
          exact ih (some first) _ _ h
      | some p =>
        rcases p with ⟨k', v'⟩
        simp only [he] at h
        split at h
        · cases h
          exact he
        · exact ih firstEmpty _ _ h

theorem probeFrom_found_cell [BEq α] (m : Raw₀ α β) (query : α) (fuel i : Nat)
    (hi : i < m.1.keyArray.size) (index : Fin m.1.keyArray.size)
    (k : α) (v : β k) (hmatch : k == query)
    (h : m.probeFrom query fuel i hi = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  exact probeFromAux_found_cell m query none fuel i hi index k v hmatch h

theorem probe_empty_cell [BEq α] [Hashable α] (m : Raw₀ α β) (query : α)
    {index : Fin m.1.keyArray.size} (h : m.probe query = .empty index) :
    m.1.entryAtInBounds? index.1 index.2 = none := by
  unfold Raw₀.probe at h
  exact probeFrom_empty_cell m query _ _ _ h

theorem probe_found_cell [BEq α] [Hashable α] (m : Raw₀ α β) (query : α)
    (index : Fin m.1.keyArray.size) (k : α) (v : β k) (hmatch : k == query)
    (h : m.probe query = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  unfold Raw₀.probe at h
  exact probeFrom_found_cell m query _ _ _ index k v hmatch h

private theorem probeFromAux_index_congr [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size)) (fuel : Nat) {i j : Nat}
    (hij : i = j) (hi : i < m.1.keyArray.size) (hj : j < m.1.keyArray.size) :
    m.probeFromAux query firstEmpty fuel i hi =
      m.probeFromAux query firstEmpty fuel j hj := by
  subst j
  have hproof : hi = hj := Subsingleton.elim _ _
  subst hj
  rfl

theorem probeFromAux_found_of_path [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size)) {fuel i target : Nat}
    (hi : i < m.1.keyArray.size)
    (path : Raw₀.ProbePath m.1.keyArray fuel i target)
    {k : α} {v : β k} (htarget : target < m.1.keyArray.size)
    (hentry : m.1.entryAtInBounds? target htarget = some ⟨k, v⟩)
    (hmatch : k == query) :
    ∃ (index : Fin m.1.keyArray.size) (key : α) (value : β key) (hkey : key == query),
      m.probeFromAux query firstEmpty fuel i hi = .found index key value hkey := by
  induction path generalizing firstEmpty with
  | @here remaining current hcurrent =>
    have hkey := keyArray_eq_some_of_entryAtInBounds_eq_some m.1 current hcurrent
      m.1.keysValues k v hentry
    refine ⟨⟨current, hcurrent⟩, k, v, hmatch, ?_⟩
    rw [Raw₀.probeFromAux.eq_def]
    simp [hkey, hentry, hmatch]
  | @next remaining current target hcurrent hkey path ih =>
    rw [Raw₀.probeFromAux.eq_def]
    cases hk : m.1.keyArray[current] with
    | none => simp [hk] at hkey
    | some storedKey =>
      simp only [hk]
      cases he : m.1.entryAtInBounds? current hcurrent with
      | none =>
        simp only
        have hproof : hi = hcurrent := Subsingleton.elim _ _
        subst hi
        let firstEmpty' : Option (Fin m.1.keyArray.size) := match firstEmpty with
          | none => some ⟨current, hcurrent⟩
          | some index => some index
        have hnext : Raw₀.nextIndexNat m.1.keyArray.size current < m.1.keyArray.size := by
          simpa only [Raw₀.nextIndex_val] using
            (Raw₀.nextIndex m.2 ⟨current, hcurrent⟩).2
        obtain ⟨index, key, value, hkey, hfound⟩ :=
          ih firstEmpty' hnext htarget hentry
        refine ⟨index, key, value, hkey, ?_⟩
        refine (probeFromAux_index_congr m query firstEmpty' remaining
          (Raw₀.nextIndex_val m.2 ⟨current, hcurrent⟩) _ hnext).trans ?_
        simpa only [firstEmpty'] using hfound
      | some p =>
        rcases p with ⟨currentKey, currentValue⟩
        simp only
        have hproof : hi = hcurrent := Subsingleton.elim _ _
        subst hi
        by_cases hmatchCurrent : currentKey == query
        · refine ⟨⟨current, hcurrent⟩, currentKey, currentValue, hmatchCurrent, ?_⟩
          simp [hmatchCurrent]
        · simp only [hmatchCurrent, Bool.false_eq_true]
          have hnext : Raw₀.nextIndexNat m.1.keyArray.size current < m.1.keyArray.size := by
            simpa only [Raw₀.nextIndex_val] using
              (Raw₀.nextIndex m.2 ⟨current, hcurrent⟩).2
          obtain ⟨index, key, value, hkey, hfound⟩ :=
            ih firstEmpty hnext htarget hentry
          refine ⟨index, key, value, hkey, ?_⟩
          exact (probeFromAux_index_congr m query firstEmpty remaining
            (Raw₀.nextIndex_val m.2 ⟨current, hcurrent⟩) _ hnext).trans hfound

theorem probe_found_of_scanFrom_found [BEq α] [Hashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) (query : α) (index : Fin m.1.keyArray.size)
    (k : α) (v : β k) (hmatch : k == query)
    (hscan : m.scanFrom query 0 = .found index k v hmatch) :
    ∃ (foundIndex : Fin m.1.keyArray.size) (foundKey : α) (foundValue : β foundKey)
        (foundMatch : foundKey == query),
      m.probe query = .found foundIndex foundKey foundValue foundMatch := by
  have hentry := scanFrom_found_cell m query 0 index k v hmatch hscan
  have hkey := keyArray_eq_some_of_entryAtInBounds_eq_some m.1 index index.isLt
    h.keysValues k v hentry
  have path := h.reachable index index.isLt k hkey query hmatch
  have path' : Raw₀.ProbePath m.1.keyArray m.1.keyArray.size
      (mkIdx m.1.keyArray.size m.2 (hash query)).1.toNat index := by
    simpa only [Raw₀.probeStart_eq_mkIdx m.2] using path
  unfold Raw₀.probe Raw₀.probeFrom
  simpa using
    probeFromAux_found_of_path m query none (mkIdx m.1.keyArray.size m.2 (hash query)).2
      path' index.isLt hentry hmatch

theorem scanFrom_absent_of_probe_not_found [BEq α] [Hashable α] (m : Raw₀ α β)
    (h : Raw.WFImp m.1) (query : α)
    (hprobe : (∃ index, m.probe query = .empty index) ∨ m.probe query = .full) :
    m.scanFrom query 0 = .absent := by
  cases hscan : m.scanFrom query 0 with
  | absent => rfl
  | found index k v hmatch =>
    obtain ⟨foundIndex, foundKey, foundValue, foundMatch, hfound⟩ :=
      probe_found_of_scanFrom_found m h query index k v hmatch hscan
    rcases hprobe with ⟨emptyIndex, hempty⟩ | hfull
    · rw [hempty] at hfound
      contradiction
    · rw [hfull] at hfound
      contradiction

theorem scan_found_cell [BEq α] [Hashable α] (m : Raw₀ α β) (query : α)
    (index : Fin m.1.keyArray.size) (k : α) (v : β k) (hmatch : k == query)
    (hscan : m.scan query = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  unfold Raw₀.scan at hscan
  cases hp : m.probe query with
  | found foundIndex foundKey foundValue foundMatch =>
    simp only [hp] at hscan
    have hcell := probe_found_cell m query foundIndex foundKey foundValue foundMatch hp
    cases hscan
    exact hcell
  | empty => simp [hp] at hscan
  | full => simp [hp] at hscan

theorem findEmptyFrom_empty_cell (m : Raw₀ α β) (i : Nat)
    {index : Fin m.1.keyArray.size} (h : m.findEmptyFrom i = .empty index) :
    m.1.entryAtInBounds? index.1 index.2 = none := by
  rw [Raw₀.findEmptyFrom.eq_def] at h
  split at h <;> rename_i hi
  · cases he : m.1.entryAtInBounds? i hi with
    | none =>
      simp only [he] at h
      cases h
      exact he
    | some p =>
      simp only [he] at h
      exact findEmptyFrom_empty_cell m (i + 1) h
  · contradiction
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem findEmpty_empty_cell (m : Raw₀ α β) {index : Fin m.1.keyArray.size}
    (h : m.findEmpty = .empty index) :
    m.1.entryAtInBounds? index.1 index.2 = none := by
  exact findEmptyFrom_empty_cell m 0 h

theorem findEmptyFrom_full_length (m : Raw₀ α β) (i : Nat)
    (h : m.findEmptyFrom i = .full) :
    (m.1.entriesFrom i).toList.length = m.1.keyArray.size - i := by
  rw [Raw₀.findEmptyFrom.eq_def] at h
  rw [Raw.entriesFrom.eq_def]
  by_cases hi : i < m.1.keyArray.size
  · rw [dite_eq_left hi] at h ⊢
    cases he : m.1.entryAtInBounds? i hi with
    | none => simp [he] at h
    | some p =>
      rcases p with ⟨k, v⟩
      simp only [he] at h ⊢
      simp only [AssocList.toList_cons, List.length_cons]
      rw [findEmptyFrom_full_length m (i + 1) h]
      omega
  · rw [dite_eq_right hi]
    simp only [AssocList.toList_nil, List.length_nil]
    omega
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem findEmpty_full_length (m : Raw₀ α β) (h : m.findEmpty = .full) :
    (m.1.entriesFrom 0).toList.length = m.1.keyArray.size := by
  simpa using findEmptyFrom_full_length m 0 h

theorem setEntry_empty_perm (b : Raw α β) (size i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray)
    (k : α) (v : β k) (hempty : b.entryAtInBounds? i hi = none) :
    ((b.setEntry size i hi k v).entriesFrom 0).toList ~
      ⟨k, v⟩ :: (b.entriesFrom 0).toList := by
  obtain ⟨pre, post, hold, hnew⟩ :=
    entriesFrom_setEntry_split b size i hi hkv k v 0 (by omega)
  rw [hempty] at hold
  rw [hnew, hold]
  simp [List.append_assoc]

theorem entryAtInBounds_mem_entries (b : Raw α β) (i : Nat) (hi : i < b.keyArray.size)
    (hkv : Raw.KeysValues b.keyArray b.valueArray)
    (k : α) (v : β k) (hentry : b.entryAtInBounds? i hi = some ⟨k, v⟩) :
    Sigma.mk k v ∈ (b.entriesFrom 0).toList := by
  obtain ⟨pre, post, hold, _⟩ :=
    entriesFrom_setEntry_split b b.size i hi hkv k v 0 (by omega)
  rw [hentry] at hold
  rw [hold]
  simp

theorem getEntry?_eq_getEntry?_entries [BEq α] [Hashable α] [EquivBEq α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (query : α) :
    m.getEntry? query = List.getEntry? query (m.1.entriesFrom 0).toList := by
  cases hp : m.probe query with
  | found index k v hmatch =>
    have hcell := probe_found_cell m query index k v hmatch hp
    have hmem := entryAtInBounds_mem_entries m.1 index index.isLt h.keysValues k v hcell
    have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
      simpa [toListModel_buckets_eq] using h.distinct
    have hget : List.getEntry? query (m.1.entriesFrom 0).toList = some ⟨k, v⟩ :=
      (List.getEntry?_eq_some_iff hd).2 ⟨BEq.symm hmatch, hmem⟩
    simp [Raw₀.getEntry?, Raw₀.scan, hp, hget]
  | empty index =>
    have hs := scanFrom_absent_of_probe_not_found m h query (.inl ⟨index, hp⟩)
    have hget := scanFrom_entry_eq_getEntry? m query 0
    rw [hs] at hget
    simpa only [Raw₀.getEntry?, Raw₀.scan, hp, scanResultEntry?] using hget
  | full =>
    have hs := scanFrom_absent_of_probe_not_found m h query (.inr hp)
    have hget := scanFrom_entry_eq_getEntry? m query 0
    rw [hs] at hget
    simpa only [Raw₀.getEntry?, Raw₀.scan, hp, scanResultEntry?] using hget

theorem contains_eq_containsKey_entries [BEq α] [Hashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (query : α) :
    m.contains query = List.containsKey query (m.1.entriesFrom 0).toList := by
  cases hp : m.probe query with
  | found index k v hmatch =>
    have hcell := probe_found_cell m query index k v hmatch hp
    have hmem := entryAtInBounds_mem_entries m.1 index index.isLt h.keysValues k v hcell
    have hc : List.containsKey query (m.1.entriesFrom 0).toList = true :=
      List.containsKey_eq_true_iff_exists_mem.2 ⟨⟨k, v⟩, hmem, hmatch⟩
    simp [Raw₀.contains, Raw₀.scan, hp, hc]
  | empty index =>
    have hs := scanFrom_absent_of_probe_not_found m h query (.inl ⟨index, hp⟩)
    have hget := scanFrom_entry_eq_getEntry? m query 0
    rw [hs] at hget
    have hc : List.containsKey query (m.1.entriesFrom 0).toList = false :=
      List.getEntry?_eq_none.mp hget.symm
    simp [Raw₀.contains, Raw₀.scan, hp, hc]
  | full =>
    have hs := scanFrom_absent_of_probe_not_found m h query (.inr hp)
    have hget := scanFrom_entry_eq_getEntry? m query 0
    rw [hs] at hget
    have hc : List.containsKey query (m.1.entriesFrom 0).toList = false :=
      List.getEntry?_eq_none.mp hget.symm
    simp [Raw₀.contains, Raw₀.scan, hp, hc]

theorem get?_eq_getValueCast?_entries [BEq α] [LawfulBEq α] [Hashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (query : α) :
    m.get? query = List.getValueCast? query (m.1.entriesFrom 0).toList := by
  cases hp : m.probe query with
  | found index k v hmatch =>
    have hcell := probe_found_cell m query index k v hmatch hp
    have hmem := entryAtInBounds_mem_entries m.1 index index.isLt h.keysValues k v hcell
    have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
      simpa [toListModel_buckets_eq] using h.distinct
    have hget : List.getEntry? query (m.1.entriesFrom 0).toList = some ⟨k, v⟩ :=
      (List.getEntry?_eq_some_iff hd).2 ⟨eq_of_beq hmatch ▸ BEq.rfl, hmem⟩
    have hk : k = query := eq_of_beq hmatch
    subst k
    rw [List.getEntry?_eq_getValueCast?] at hget
    cases hv : List.getValueCast? query (m.1.entriesFrom 0).toList with
    | none => simp [hv] at hget
    | some value =>
      simp only [hv, Option.map_some, Option.some.injEq] at hget
      cases hget
      simp [Raw₀.get?, Raw₀.scan, hp]
  | empty index =>
    have hs := scanFrom_absent_of_probe_not_found m h query (.inl ⟨index, hp⟩)
    have hget := scanFrom_valueCast_eq_getValueCast? m query 0
    rw [hs] at hget
    simpa only [Raw₀.get?, Raw₀.scan, hp, scanResultValueCast?] using hget
  | full =>
    have hs := scanFrom_absent_of_probe_not_found m h query (.inr hp)
    have hget := scanFrom_valueCast_eq_getValueCast? m query 0
    rw [hs] at hget
    simpa only [Raw₀.get?, Raw₀.scan, hp, scanResultValueCast?] using hget

theorem setEntry_replace_perm [BEq α] [EquivBEq α] (b : Raw α β) (size i : Nat)
    (hi : i < b.keyArray.size) (hkv : Raw.KeysValues b.keyArray b.valueArray)
    (k : α) (v : β k) (oldKey : α) (oldValue : β oldKey)
    (hentry : b.entryAtInBounds? i hi = some ⟨oldKey, oldValue⟩)
    (hmatch : oldKey == k) (hd : Std.Internal.List.DistinctKeys (b.entriesFrom 0).toList) :
    ((b.setEntry size i hi k v).entriesFrom 0).toList ~
      List.replaceEntry k v (b.entriesFrom 0).toList := by
  obtain ⟨pre, post, hold, hnew⟩ :=
    entriesFrom_setEntry_split b size i hi hkv k v 0 (by omega)
  rw [hentry] at hold
  have hpold : (b.entriesFrom 0).toList ~
      ⟨oldKey, oldValue⟩ :: (pre ++ post) := by
    rw [hold]
    simp [List.append_assoc]
  have hpnew : ((b.setEntry size i hi k v).entriesFrom 0).toList ~
      ⟨k, v⟩ :: (pre ++ post) := by
    rw [hnew]
    simp [List.append_assoc]
  refine hpnew.trans ?_
  have hp := (List.replaceEntry_of_perm (k := k) (v := v) hd hpold).symm
  rw [← List.replaceEntry_cons_of_true hmatch]
  exact hp

theorem clearCell_erase_perm [BEq α] [EquivBEq α] (b : Raw α β) (size i : Nat)
    (hi : i < b.keyArray.size) (hkv : Raw.KeysValues b.keyArray b.valueArray)
    (query oldKey : α) (oldValue : β oldKey)
    (hentry : b.entryAtInBounds? i hi = some ⟨oldKey, oldValue⟩)
    (hmatch : oldKey == query) (hd : Std.Internal.List.DistinctKeys (b.entriesFrom 0).toList) :
    ((b.clearCell size i hi).entriesFrom 0).toList ~
      List.eraseKey query (b.entriesFrom 0).toList := by
  obtain ⟨pre, post, hold, hnew⟩ :=
    entriesFrom_clearCell_split b size i hi hkv 0 (by omega)
  rw [hentry] at hold
  have hpold : (b.entriesFrom 0).toList ~
      ⟨oldKey, oldValue⟩ :: (pre ++ post) := by
    rw [hold]
    simp [List.append_assoc]
  rw [hnew]
  have hp := (List.eraseKey_of_perm (k := query) hd hpold).symm
  have herase : List.eraseKey query (⟨oldKey, oldValue⟩ :: (pre ++ post)) = pre ++ post :=
    List.eraseKey_cons_of_beq hmatch
  exact (List.Perm.of_eq herase.symm).trans hp

theorem insertNoExpand_entries_perm [BEq α] [Hashable α] [EquivBEq α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) (b : β a) :
    ((m.insertNoExpand a b).1.entriesFrom 0).toList ~
      List.insertEntry a b (m.1.entriesFrom 0).toList := by
  cases hp : m.probe a with
  | found index k v hmatch =>
    rw [Raw₀.insertNoExpand, hp]
    have hcell := probe_found_cell m a index k v hmatch hp
    have hmem := entryAtInBounds_mem_entries m.1 index index.isLt h.keysValues k v hcell
    have hc : List.containsKey a (m.1.entriesFrom 0).toList :=
      List.containsKey_of_beq (List.containsKey_of_mem hmem) hmatch
    rw [List.insertEntry_of_containsKey hc]
    have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
      simpa [toListModel_buckets_eq] using h.distinct
    exact setEntry_replace_perm m.1 m.1.size index index.isLt h.keysValues a b k v hcell hmatch hd
  | empty index =>
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = false := by
      rw [← contains_eq_containsKey_entries m h a]
      simp [Raw₀.contains, Raw₀.scan, hp]
    rw [List.insertEntry_of_containsKey_eq_false hc]
    rw [Raw₀.insertNoExpand, hp]
    exact setEntry_empty_perm m.1 (m.1.size + 1) index index.isLt h.keysValues a b
      (probe_empty_cell m a hp)
  | full =>
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = false := by
      rw [← contains_eq_containsKey_entries m h a]
      simp [Raw₀.contains, Raw₀.scan, hp]
    rw [List.insertEntry_of_containsKey_eq_false hc]
    cases hf : m.findEmpty with
    | empty index =>
      rw [Raw₀.insertNoExpand, hp, hf]
      exact setEntry_empty_perm m.1 (m.1.size + 1) index index.isLt h.keysValues a b
        (findEmpty_empty_cell m hf)
    | full =>
      have hlen := findEmpty_full_length m hf
      have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
        simpa [toListModel_buckets_eq] using h.size_eq
      have hlt := h.size_lt
      rw [hsize, hlen] at hlt
      exact (Nat.lt_irrefl _ hlt).elim

theorem size_insertNoExpand_eq_length_insertEntry [BEq α] [Hashable α] [EquivBEq α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) (b : β a) :
    (m.insertNoExpand a b).1.size =
      (List.insertEntry a b (m.1.entriesFrom 0).toList).length := by
  have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
    simpa [toListModel_buckets_eq] using h.size_eq
  cases hp : m.probe a with
  | found index k v hmatch =>
    rw [Raw₀.insertNoExpand, hp, List.length_insertEntry]
    have hcell := probe_found_cell m a index k v hmatch hp
    have hmem := entryAtInBounds_mem_entries m.1 index index.isLt h.keysValues k v hcell
    have hc : List.containsKey a (m.1.entriesFrom 0).toList :=
      List.containsKey_of_beq (List.containsKey_of_mem hmem) hmatch
    simp [hc, hsize, Raw.setEntry, Raw.setCell]
  | empty index =>
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = false := by
      rw [← contains_eq_containsKey_entries m h a]
      simp [Raw₀.contains, Raw₀.scan, hp]
    rw [List.length_insertEntry, hc]
    rw [Raw₀.insertNoExpand, hp]
    exact congrArg (· + 1) hsize
  | full =>
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = false := by
      rw [← contains_eq_containsKey_entries m h a]
      simp [Raw₀.contains, Raw₀.scan, hp]
    rw [List.length_insertEntry, hc]
    cases hf : m.findEmpty with
    | empty index =>
      rw [Raw₀.insertNoExpand, hp, hf]
      exact congrArg (· + 1) hsize
    | full =>
      have hlen := findEmpty_full_length m hf
      have hlt := h.size_lt
      rw [hsize, hlen] at hlt
      exact (Nat.lt_irrefl _ hlt).elim

@[simp] theorem keyArray_size_insertNoExpand [BEq α] [Hashable α]
    (m : Raw₀ α β) (a : α) (b : β a) :
    (m.insertNoExpand a b).1.keyArray.size = m.1.keyArray.size := by
  cases hp : m.probe a with
  | found => simp [Raw₀.insertNoExpand, hp, Raw.setEntry, Raw.setCell]
  | empty => simp [Raw₀.insertNoExpand, hp, Raw.setEntry, Raw.setCell]
  | full =>
    cases hf : m.findEmpty <;>
      simp [Raw₀.insertNoExpand, hp, hf, Raw.setEntry, Raw.setCell]

theorem keysValues_insertNoExpand [BEq α] [Hashable α]
    (m : Raw₀ α β) (hkv : Raw.KeysValues m.1.keyArray m.1.valueArray)
    (a : α) (b : β a) :
    Raw.KeysValues (m.insertNoExpand a b).1.keyArray (m.insertNoExpand a b).1.valueArray := by
  cases hp : m.probe a with
  | found index k v hmatch =>
    rw [Raw₀.insertNoExpand, hp]
    exact keysValues_setEntry m.1 m.1.size index index.isLt hkv a b
  | empty index =>
    rw [Raw₀.insertNoExpand, hp]
    exact keysValues_setEntry m.1 (m.1.size + 1) index index.isLt hkv a b
  | full =>
    cases hf : m.findEmpty with
    | empty index =>
      rw [Raw₀.insertNoExpand, hp, hf]
      exact keysValues_setEntry m.1 (m.1.size + 1) index index.isLt hkv a b
    | full =>
      simpa [Raw₀.insertNoExpand, hp, hf] using hkv

theorem reachable_insertNoExpand [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) (b : β a) :
    ∀ (i : Nat) (hi : i < (m.insertNoExpand a b).1.keyArray.size) (k : α),
      (m.insertNoExpand a b).1.keyArray[i] = .some k →
      ∀ (query : α), k == query →
        Raw₀.ProbePath (m.insertNoExpand a b).1.keyArray
          (m.insertNoExpand a b).1.keyArray.size
          (Raw₀.probeStart (m.insertNoExpand a b).1.keyArray.size (hash query)) i := by
  cases hp : m.probe a with
  | found index oldKey oldValue hmatch =>
    rw [Raw₀.insertNoExpand, hp]
    have hentry := probe_found_cell m a index oldKey oldValue hmatch hp
    have hkey := keyArray_eq_some_of_entryAtInBounds_eq_some m.1 index index.isLt
      h.keysValues oldKey oldValue hentry
    exact reachable_setEntry m h m.1.size index index.isLt a b (by
      intro query haquery
      exact h.reachable index index.isLt oldKey hkey query (BEq.trans hmatch haquery))
  | empty index =>
    rw [Raw₀.insertNoExpand, hp]
    exact reachable_setEntry m h (m.1.size + 1) index index.isLt a b (by
      intro query haquery
      simpa [hash_eq haquery] using probe_empty_path m a hp)
  | full =>
    cases hf : m.findEmpty with
    | empty index =>
      rw [Raw₀.insertNoExpand, hp, hf]
      exact reachable_setEntry m h (m.1.size + 1) index index.isLt a b (by
        intro query haquery
        simpa [hash_eq haquery] using probe_full_path m a hp index index.isLt)
    | full =>
      simpa [Raw₀.insertNoExpand, hp, hf] using h.reachable

theorem wfImp_insertNoExpand [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) (b : β a)
    (hroom : m.1.size + 1 < m.1.keyArray.size) :
    Raw.WFImp (m.insertNoExpand a b).1 := by
  have hp := insertNoExpand_entries_perm m h a b
  have hcache := size_insertNoExpand_eq_length_insertEntry m h a b
  have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
    simpa [toListModel_buckets_eq] using h.size_eq
  refine { cells_pos := ?_, keysValues := ?_, size_eq := ?_, distinct := ?_, size_lt := ?_, reachable := ?_ }
  · simpa using m.2
  · exact keysValues_insertNoExpand m h.keysValues a b
  · rw [toListModel_buckets_eq]
    exact hcache.trans hp.length_eq.symm
  · rw [toListModel_buckets_eq]
    have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
      simpa [toListModel_buckets_eq] using h.distinct
    exact hd.insertEntry.perm hp
  · rw [keyArray_size_insertNoExpand, hcache, List.length_insertEntry, ← hsize]
    split <;> omega
  · exact reachable_insertNoExpand m h a b

theorem size_insertNoExpand_le [BEq α] [Hashable α] [EquivBEq α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) (b : β a) :
    (m.insertNoExpand a b).1.size ≤ m.1.size + 1 := by
  rw [size_insertNoExpand_eq_length_insertEntry m h]
  apply Nat.le_trans List.length_insertEntry_le
  have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
    simpa [toListModel_buckets_eq] using h.size_eq
  rw [← hsize]
  exact Nat.le_refl _

theorem foldl_insertNoExpand [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (l : List ((a : α) × β a)) (m : Raw₀ α β) (h : Raw.WFImp m.1)
    (hspace : m.1.size + l.length + 1 < m.1.keyArray.size) :
    let result := l.foldl (fun m p => m.insertNoExpand p.1 p.2) m
    Raw.WFImp result.1 ∧
      (result.1.entriesFrom 0).toList ~
        List.insertList (m.1.entriesFrom 0).toList l := by
  induction l generalizing m with
  | nil =>
    exact ⟨h, .rfl⟩
  | cons p l ih =>
    rcases p with ⟨a, b⟩
    simp only [List.length_cons] at hspace
    have hroom : m.1.size + 1 < m.1.keyArray.size := by omega
    have hnext := wfImp_insertNoExpand m h a b hroom
    have hle := size_insertNoExpand_le m h a b
    have hspace' :
        (m.insertNoExpand a b).1.size + l.length + 1 <
          (m.insertNoExpand a b).1.keyArray.size := by
      rw [keyArray_size_insertNoExpand]
      omega
    obtain ⟨hwf, hp⟩ := ih (m := m.insertNoExpand a b) hnext hspace'
    refine ⟨hwf, hp.trans ?_⟩
    apply List.insertList_perm_of_perm_first
    · exact insertNoExpand_entries_perm m h a b
    · simpa [toListModel_buckets_eq] using hnext.distinct

theorem AssocList.idRun_foldlM {gamma : Type w}
    (f : gamma → (a : α) → β a → gamma) (init : gamma) (l : AssocList α β) :
    Id.run (l.foldlM (fun acc k v => pure (f acc k v)) init) =
      l.toList.foldl (fun acc p => f acc p.1 p.2) init := by
  induction l generalizing init with
  | nil => rfl
  | cons k v l ih =>
    change Id.run (l.foldlM (fun acc k v => pure (f acc k v)) (f init k v)) =
      l.toList.foldl (fun acc p => f acc p.1 p.2) (f init k v)
    exact ih (f init k v)

theorem Raw.fold_eq_foldl_entries {gamma : Type w}
    (f : gamma → (a : α) → β a → gamma) (init : gamma) (m : Raw α β) :
    m.fold f init =
      (m.entriesFrom 0).toList.foldl (fun acc p => f acc p.1 p.2) init := by
  simp only [Raw.fold, Raw.foldM, foldMFrom_eq_foldlM]
  exact AssocList.idRun_foldlM f init (m.entriesFrom 0)

theorem Raw.equiv_iff_toListModel_perm {m₁ m₂ : Raw α β} :
    m₁.Equiv m₂ ↔ toListModel m₁.buckets ~ toListModel m₂.buckets :=
  ⟨Raw.Equiv.impl, Raw.Equiv.mk⟩

theorem Raw.size_eq_length [BEq α] [Hashable α] {m : Raw α β} (h : Raw.WFImp m) :
    m.size = (toListModel m.buckets).length := h.size_eq

theorem Raw.isEmpty_eq_isEmpty [BEq α] [Hashable α] {m : Raw α β} (h : Raw.WFImp m) :
    m.isEmpty = (toListModel m.buckets).isEmpty := by
  rw [Raw.isEmpty, Bool.eq_iff_iff, List.isEmpty_iff_length_eq_zero, h.size_eq,
    Nat.beq_eq_true_eq]

theorem AssocList.foldlM_eq_foldlM_toList {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n] (f : gamma → (a : α) → β a → n gamma)
    (init : gamma) (l : AssocList α β) :
    l.foldlM f init = l.toList.foldlM (fun acc p => f acc p.1 p.2) init := by
  induction l generalizing init with
  | nil => rfl
  | cons k v l ih =>
    change (f init k v >>= fun init' => l.foldlM f init') =
      (f init k v >>= fun init' => l.toList.foldlM (fun acc p => f acc p.1 p.2) init')
    congr 1
    funext init'
    exact ih init'

theorem Raw.foldM_eq_foldlM_toListModel {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n] {f : gamma → (a : α) → β a → n gamma}
    {init : gamma} {b : Raw α β} :
    b.foldM f init =
      (toListModel b.buckets).foldlM (fun acc p => f acc p.1 p.2) init := by
  rw [Raw.foldM, foldMFrom_eq_foldlM, AssocList.foldlM_eq_foldlM_toList,
    toListModel_buckets_eq]

theorem Raw.fold_eq_foldl_toListModel {gamma : Type w} {b : Raw α β}
    {f : gamma → (a : α) → β a → gamma} {init : gamma} :
    b.fold f init =
      (toListModel b.buckets).foldl (fun acc p => f acc p.1 p.2) init := by
  rw [Raw.fold_eq_foldl_entries, toListModel_buckets_eq]

theorem Raw.fold_induction {gamma : Type w}
    {f : gamma → (a : α) → β a → gamma} {init : gamma} {b : Raw α β}
    {P : gamma → Prop} (base : P init)
    (step : ∀ acc a b, P acc → P (f acc a b)) : P (b.fold f init) := by
  rw [Raw.fold_eq_foldl_toListModel]
  generalize toListModel b.buckets = l
  induction l generalizing init with
  | nil => exact base
  | cons p l ih =>
    exact ih (step init p.1 p.2 base)

theorem foldRevMFrom_eq_def {gamma : Type w} {n : Type w → Type w'} [Monad n]
    (f : gamma → (a : α) → β a → n gamma) (b : Raw α β)
    (acc : gamma) (i : Nat) :
    b.foldRevMFrom f acc i =
      if h : i < b.keyArray.size then
        match b.entryAtInBounds? i h with
        | .none => b.foldRevMFrom f acc (i + 1)
        | .some ⟨k, v⟩ => b.foldRevMFrom f acc (i + 1) >>= fun acc => f acc k v
      else
        pure acc := by
  exact Raw.foldRevMFrom.eq_def f b acc i

theorem foldRevMFrom_eq_foldrM {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n] (f : gamma → (a : α) → β a → n gamma)
    (b : Raw α β) (acc : gamma) (i : Nat) :
    b.foldRevMFrom f acc i =
      (b.entriesFrom i).foldrM (fun k v acc => f acc k v) acc := by
  rw [foldRevMFrom_eq_def, Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · cases he : b.entryAtInBounds? i hi with
    | none =>
      rw [foldRevMFrom_eq_foldrM]
    | some p =>
      rcases p with ⟨k, v⟩
      change (b.foldRevMFrom f acc (i + 1) >>= fun acc' => f acc' k v) =
        ((b.entriesFrom (i + 1)).foldrM (fun k v acc => f acc k v) acc >>=
          fun acc' => f acc' k v)
      rw [foldRevMFrom_eq_foldrM]
  · change pure acc = pure acc
    rfl
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem AssocList.foldrM_eq_foldrM_toList {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n] (f : gamma → (a : α) → β a → n gamma)
    (init : gamma) (l : AssocList α β) :
    l.foldrM (fun k v acc => f acc k v) init =
      l.toList.foldrM (fun p acc => f acc p.1 p.2) init := by
  induction l generalizing init with
  | nil => rfl
  | cons k v l ih =>
    have hfold : AssocList.foldrM (fun k v acc => f acc k v) init (.cons k v l) =
        (l.foldrM (fun k v acc => f acc k v) init >>= fun acc' => f acc' k v) := rfl
    rw [hfold, AssocList.toList_cons, List.foldrM_cons]
    exact congrArg (fun x => x >>= fun acc' => f acc' k v) (ih init)

theorem Raw.foldRevM_eq_foldrM_toListModel {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n] {f : gamma → (a : α) → β a → n gamma}
    {init : gamma} {b : Raw α β} :
    Raw.Internal.foldRevM f init b =
      (toListModel b.buckets).foldrM (fun p acc => f acc p.1 p.2) init := by
  rw [Raw.Internal.foldRevM, foldRevMFrom_eq_foldrM,
    AssocList.foldrM_eq_foldrM_toList, toListModel_buckets_eq]

theorem Raw.foldRev_eq_foldr_toListModel {gamma : Type w} {b : Raw α β}
    {f : gamma → (a : α) → β a → gamma} {init : gamma} :
    Raw.Internal.foldRev f init b =
      (toListModel b.buckets).foldr (fun p acc => f acc p.1 p.2) init := by
  simp [Raw.Internal.foldRev, Raw.foldRevM_eq_foldrM_toListModel]

theorem Raw.toList_eq_toListModel {m : Raw α β} :
    m.toList = toListModel m.buckets := by
  simp [Raw.toList, Raw.foldRev_eq_foldr_toListModel]

theorem Raw.Const.toList_eq_toListModel_map {gamma : Type v}
    {m : Raw α (fun _ => gamma)} :
    Raw.Const.toList m = (toListModel m.buckets).map (fun ⟨k, v⟩ => (k, v)) := by
  simp [Raw.Const.toList, Raw.foldRev_eq_foldr_toListModel]

theorem Raw.keys_eq_keys_toListModel {m : Raw α β} :
    m.keys = List.keys (toListModel m.buckets) := by
  simp [Raw.keys, Raw.foldRev_eq_foldr_toListModel, List.keys_eq_map]

theorem Raw.values_eq_values_toListModel {gamma : Type v}
    {m : Raw α (fun _ => gamma)} :
    m.values = List.values (toListModel m.buckets) := by
  simp [Raw.values, Raw.foldRev_eq_foldr_toListModel, List.values_eq_map]

theorem Raw.toArray_eq_toArray_toListModel {m : Raw α β} :
    m.toArray = (toListModel m.buckets).toArray := by
  simp [Raw.toArray, Raw.fold_eq_foldl_toListModel, List.foldl_push_eq_append]

theorem Raw.Const.toArray_eq_toArray_map_toListModel {gamma : Type v}
    {m : Raw α (fun _ => gamma)} :
    Raw.Const.toArray m =
      ((toListModel m.buckets).map (fun ⟨k, v⟩ => (k, v))).toArray := by
  simp [Raw.Const.toArray, Raw.fold_eq_foldl_toListModel, List.foldl_push_eq_append]

theorem Raw.keysArray_eq_toArray_keys_toListModel {m : Raw α β} :
    m.keysArray = (List.keys (toListModel m.buckets)).toArray := by
  simp [Raw.keysArray, Raw.fold_eq_foldl_toListModel, List.foldl_push_eq_append,
    List.keys_eq_map]

theorem Raw.forM_eq_forM_toListModel {n : Type w → Type w'} [Monad n] [LawfulMonad n]
    {m : Raw α β} {f : (a : α) → β a → n PUnit} :
    m.forM f = (toListModel m.buckets).forM (fun p => f p.1 p.2) := by
  rw [Raw.forM, Raw.foldM_eq_foldlM_toListModel]
  generalize toListModel m.buckets = l
  induction l with
  | nil => simp
  | cons p l ih => simp [List.forM_eq_forM, ih]

theorem forInFrom_eq_forIn {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n]
    (f : (a : α) → β a → gamma → n (ForInStep gamma))
    (b : Raw α β) (acc : gamma) (i : Nat) :
    b.forInFrom f acc i =
      ForIn.forIn (b.entriesFrom i).toList acc (fun p acc => f p.1 p.2 acc) := by
  rw [Raw.forInFrom.eq_def, Raw.entriesFrom.eq_def]
  split <;> rename_i hi
  · cases he : b.entryAtInBounds? i hi with
    | none =>
      rw [forInFrom_eq_forIn]
    | some p =>
      rcases p with ⟨k, v⟩
      rw [AssocList.toList_cons, List.forIn_cons]
      change (f k v acc >>= fun step => match step with
          | .done acc => pure acc
          | .yield acc => b.forInFrom f acc (i + 1)) = _
      congr 1
      funext step
      cases step with
      | done acc => rfl
      | yield acc =>
        exact forInFrom_eq_forIn f b acc (i + 1)
  · change pure acc = pure acc
    rfl
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ ‹_›

theorem Raw.forIn_eq_forIn_toListModel {gamma : Type w} {n : Type w → Type w'}
    [Monad n] [LawfulMonad n] {b : Raw α β}
    {f : (a : α) → β a → gamma → n (ForInStep gamma)} {init : gamma} :
    b.forIn f init =
      ForIn.forIn (toListModel b.buckets) init (fun p acc => f p.1 p.2 acc) := by
  rw [Raw.forIn, forInFrom_eq_forIn, toListModel_buckets_eq]

theorem Raw.all_eq_all_toListModel {p : (a : α) → β a → Bool} {m : Raw α β} :
    m.all p = (toListModel m.buckets).all (fun x => p x.1 x.2) := by
  simp only [Raw.all, ForIn.forIn, Bool.not_eq_true, Id.run_bind]
  rw [Raw.forIn_eq_forIn_toListModel, ← Raw.toList_eq_toListModel, forIn_eq_forIn']
  induction m.toList with
  | nil => simp only [List.all_nil, forIn'_nil, Id.run_pure]
  | cons hd tl ih =>
    simp only [forIn'_eq_forIn, List.all_cons]
    by_cases h : p hd.fst hd.snd = false
    · simp [h]
    · simp only [forIn'_eq_forIn] at ih
      simp [h, ih]

theorem toListModel_buckets_emptyWithCapacity {c : Nat} :
    toListModel (Raw₀.emptyWithCapacity c : Raw₀ α β).1.buckets = [] := by
  unfold Raw₀.emptyWithCapacity
  apply emptyWithCellCount_toListModel

theorem wfImp_emptyWithCellCount [BEq α] [Hashable α] {n : Nat} (hn : 0 < n) :
    Raw.WFImp (Raw₀.emptyWithCellCount n hn : Raw₀ α β).1 := by
  refine { cells_pos := ?_, keysValues := ?_, size_eq := ?_, distinct := ?_, size_lt := ?_, reachable := ?_ }
  · simpa [Raw₀.emptyWithCellCount] using hn
  · exact Raw.keysValues_replicate n
  · rw [emptyWithCellCount_toListModel]
    rfl
  · rw [emptyWithCellCount_toListModel]
    exact .nil
  · simpa [Raw₀.emptyWithCellCount] using hn
  · intro i hi k hkey
    simp [Raw₀.emptyWithCellCount] at hkey

theorem wfImp_emptyWithCapacity [BEq α] [Hashable α] {c : Nat} :
    Raw.WFImp (Raw₀.emptyWithCapacity c : Raw₀ α β).1 := by
  refine { cells_pos := ?_, keysValues := ?_, size_eq := ?_, distinct := ?_, size_lt := ?_, reachable := ?_ }
  · exact (Raw₀.emptyWithCapacity c : Raw₀ α β).2
  · unfold Raw₀.emptyWithCapacity
    exact Raw.keysValues_replicate _
  · rw [toListModel_buckets_emptyWithCapacity]
    rfl
  · simp [toListModel_buckets_emptyWithCapacity]
  · simpa [Raw₀.emptyWithCapacity, Raw₀.emptyWithCellCount] using
      (Raw₀.emptyWithCapacity c : Raw₀ α β).2
  · intro i hi k hkey
    simp [Raw₀.emptyWithCapacity, Raw₀.emptyWithCellCount] at hkey

theorem expand_eq_foldl [BEq α] [Hashable α] (m : Raw₀ α β) :
    m.expand =
      (m.1.entriesFrom 0).toList.foldl
        (fun target p => target.insertNoExpand p.1 p.2)
        (Raw₀.emptyWithCellCount (m.1.keyArray.size * 2)
          (Nat.mul_pos m.2 Nat.two_pos)) := by
  simp [Raw₀.expand, Raw.fold_eq_foldl_entries]

theorem wfImp_expand [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) : Raw.WFImp m.expand.1 := by
  let hn := Nat.mul_pos m.2 Nat.two_pos
  let target : Raw₀ α β := Raw₀.emptyWithCellCount (m.1.keyArray.size * 2) hn
  have ht : Raw.WFImp target.1 := wfImp_emptyWithCellCount hn
  have hlen : (m.1.entriesFrom 0).toList.length = m.1.size := by
    simpa [toListModel_buckets_eq] using h.size_eq.symm
  have hspace :
      target.1.size + (m.1.entriesFrom 0).toList.length + 1 <
        target.1.keyArray.size := by
    have htargetSize : target.1.size = 0 := by
      simp [target, Raw₀.emptyWithCellCount]
    have htargetCells : target.1.keyArray.size = m.1.keyArray.size * 2 := by
      simp [target, Raw₀.emptyWithCellCount]
    rw [htargetSize, htargetCells, hlen]
    have hlt := h.size_lt
    omega
  rw [expand_eq_foldl]
  exact (foldl_insertNoExpand (m.1.entriesFrom 0).toList target ht hspace).1

theorem toListModel_expand [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) :
    toListModel m.expand.1.buckets ~ toListModel m.1.buckets := by
  let hn := Nat.mul_pos m.2 Nat.two_pos
  let target : Raw₀ α β := Raw₀.emptyWithCellCount (m.1.keyArray.size * 2) hn
  have ht : Raw.WFImp target.1 := wfImp_emptyWithCellCount hn
  have hlen : (m.1.entriesFrom 0).toList.length = m.1.size := by
    simpa [toListModel_buckets_eq] using h.size_eq.symm
  have hspace :
      target.1.size + (m.1.entriesFrom 0).toList.length + 1 <
        target.1.keyArray.size := by
    have htargetSize : target.1.size = 0 := by
      simp [target, Raw₀.emptyWithCellCount]
    have htargetCells : target.1.keyArray.size = m.1.keyArray.size * 2 := by
      simp [target, Raw₀.emptyWithCellCount]
    rw [htargetSize, htargetCells, hlen]
    have hlt := h.size_lt
    omega
  have hp := (foldl_insertNoExpand (m.1.entriesFrom 0).toList target ht hspace).2
  rw [expand_eq_foldl, toListModel_buckets_eq]
  refine hp.trans ?_
  have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
    simpa [toListModel_buckets_eq] using h.distinct
  have hpInsert := List.perm_insertList
    (l := ([] : List ((a : α) × β a)))
    (toInsert := (m.1.entriesFrom 0).toList) (.nil) (DistinctKeys.def.mp hd) (by simp)
  have htarget : target.1.entriesFrom 0 = .nil := by
    exact entriesFrom_emptyWithCellCount hn 0
  rw [htarget]
  simpa [toListModel_buckets_eq] using hpInsert

theorem size_expand [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) : m.expand.1.size = m.1.size := by
  rw [(wfImp_expand m h).size_eq, h.size_eq]
  exact (toListModel_expand m h).length_eq

theorem keyArray_size_foldl_insertNoExpand [BEq α] [Hashable α]
    (l : List ((a : α) × β a)) (m : Raw₀ α β) :
    (l.foldl (fun m p => m.insertNoExpand p.1 p.2) m).1.keyArray.size =
      m.1.keyArray.size := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldl_cons, ih, keyArray_size_insertNoExpand]

@[simp] theorem keyArray_size_expand [BEq α] [Hashable α] (m : Raw₀ α β) :
    m.expand.1.keyArray.size = m.1.keyArray.size * 2 := by
  rw [expand_eq_foldl, keyArray_size_foldl_insertNoExpand]
  simp [Raw₀.emptyWithCellCount]

theorem toListModel_expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) :
    toListModel m.expandIfNecessary.1.buckets ~ toListModel m.1.buckets := by
  simp only [Raw₀.expandIfNecessary]
  split
  · exact .rfl
  · exact toListModel_expand m h

theorem wfImp_expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) : Raw.WFImp m.expandIfNecessary.1 := by
  simp only [Raw₀.expandIfNecessary]
  split
  · exact h
  · exact wfImp_expand m h

theorem size_expandIfNecessary [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) :
    m.expandIfNecessary.1.size = m.1.size := by
  simp only [Raw₀.expandIfNecessary]
  split
  · rfl
  · exact size_expand m h

theorem expandIfNecessary_room [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) :
    m.expandIfNecessary.1.size + 1 < m.expandIfNecessary.1.keyArray.size := by
  simp only [Raw₀.expandIfNecessary]
  split <;> rename_i hcheck
  · exact hcheck.1
  · rw [size_expand m h, keyArray_size_expand]
    have hlt := h.size_lt
    omega

theorem toListModel_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    toListModel (m.insert a b).1.buckets ~
      List.insertEntry a b (toListModel m.1.buckets) := by
  cases hs : m.scan a with
  | found index k v hmatch =>
    have hcell := scan_found_cell m a index k v hmatch hs
    have hmem := entryAtInBounds_mem_entries m.1 index index.isLt h.keysValues k v hcell
    have hc : List.containsKey a (m.1.entriesFrom 0).toList :=
      List.containsKey_of_beq (List.containsKey_of_mem hmem) hmatch
    have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
      simpa [toListModel_buckets_eq] using h.distinct
    rw [Raw₀.insert, hs, toListModel_buckets_eq, toListModel_buckets_eq,
      List.insertEntry_of_containsKey hc]
    exact setEntry_replace_perm m.1 m.1.size index index.isLt h.keysValues a b k v
      hcell hmatch hd
  | absent =>
    let grown := m.expandIfNecessary
    have hgrown := wfImp_expandIfNecessary m h
    have hpGrown := toListModel_expandIfNecessary m h
    have hpInsert := insertNoExpand_entries_perm grown hgrown a b
    rw [Raw₀.insert, hs, toListModel_buckets_eq]
    refine hpInsert.trans ?_
    apply List.insertEntry_of_perm
    · simpa [toListModel_buckets_eq] using hgrown.distinct
    · simpa [grown, toListModel_buckets_eq] using hpGrown

theorem wfImp_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.insert a b).1 := by
  cases hs : m.scan a with
  | found index k v hmatch =>
    rw [Raw₀.insert, hs]
    have hcell := scan_found_cell m a index k v hmatch hs
    have hp := setEntry_replace_perm m.1 m.1.size index index.isLt h.keysValues a b k v
      hcell hmatch
      (by simpa [toListModel_buckets_eq] using h.distinct)
    have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
      simpa [toListModel_buckets_eq] using h.size_eq
    refine { cells_pos := ?_, keysValues := ?_, size_eq := ?_, distinct := ?_, size_lt := ?_, reachable := ?_ }
    · simpa [Raw.setEntry, Raw.setCell] using m.2
    · exact keysValues_setEntry m.1 m.1.size index index.isLt h.keysValues a b
    · rw [toListModel_buckets_eq]
      change m.1.size = ((m.1.setEntry m.1.size index index.isLt a b).entriesFrom 0).toList.length
      rw [hp.length_eq, List.length_replaceEntry]
      exact hsize
    · rw [toListModel_buckets_eq]
      have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
        simpa [toListModel_buckets_eq] using h.distinct
      exact hd.replaceEntry.perm hp
    · simpa [Raw.setEntry, Raw.setCell] using h.size_lt
    · have hkey := keyArray_eq_some_of_entryAtInBounds_eq_some m.1 index index.isLt
        h.keysValues k v hcell
      exact reachable_setEntry m h m.1.size index index.isLt a b (by
        intro query haquery
        exact h.reachable index index.isLt k hkey query (BEq.trans hmatch haquery))
  | absent =>
    rw [Raw₀.insert, hs]
    exact wfImp_insertNoExpand m.expandIfNecessary (wfImp_expandIfNecessary m h) a b
      (expandIfNecessary_room m h)

theorem toListModel_erase [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} {a : α} (h : Raw.WFImp m.1) :
    toListModel (m.erase a).1.buckets ~
      List.eraseKey a (toListModel m.1.buckets) := by
  have hd : Std.Internal.List.DistinctKeys (m.1.entriesFrom 0).toList := by
    simpa [toListModel_buckets_eq] using h.distinct
  cases hs : m.scan a with
  | found index k v hmatch =>
    have hcell := scan_found_cell m a index k v hmatch hs
    rw [Raw₀.erase, hs, toListModel_buckets_eq, toListModel_buckets_eq]
    exact clearCell_erase_perm m.1 (m.1.size - 1) index index.isLt h.keysValues a k v
      hcell hmatch hd
  | absent =>
    have hcRaw : m.contains a = false := by
      simp [Raw₀.contains, hs]
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = false := by
      rw [← contains_eq_containsKey_entries m h a]
      exact hcRaw
    have hc' : List.containsKey a (toListModel m.1.buckets) = false := by
      simpa [toListModel_buckets_eq] using hc
    rw [Raw₀.erase, hs, List.eraseKey_of_containsKey_eq_false hc']

@[simp] theorem keyArray_size_erase [BEq α] [Hashable α]
    (m : Raw₀ α β) (a : α) :
    (m.erase a).1.keyArray.size = m.1.keyArray.size := by
  cases hs : m.scan a with
  | found => simp [Raw₀.erase, hs, Raw.clearCell]
  | absent => simp [Raw₀.erase, hs]

theorem keysValues_erase [BEq α] [Hashable α]
    (m : Raw₀ α β) (hkv : Raw.KeysValues m.1.keyArray m.1.valueArray) (a : α) :
    Raw.KeysValues (m.erase a).1.keyArray (m.erase a).1.valueArray := by
  cases hs : m.scan a with
  | found index k v hmatch =>
    rw [Raw₀.erase, hs]
    exact keysValues_clearCell m.1 (m.1.size - 1) index index.isLt hkv
  | absent =>
    simpa [Raw₀.erase, hs] using hkv

theorem size_erase_eq_length_eraseKey [BEq α] [Hashable α] [EquivBEq α]
    (m : Raw₀ α β) (h : Raw.WFImp m.1) (a : α) :
    (m.erase a).1.size =
      (List.eraseKey a (m.1.entriesFrom 0).toList).length := by
  have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
    simpa [toListModel_buckets_eq] using h.size_eq
  cases hs : m.scan a with
  | found index k v hmatch =>
    have hcRaw : m.contains a = true := by
      simp [Raw₀.contains, hs]
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = true := by
      rw [← contains_eq_containsKey_entries m h a]
      exact hcRaw
    simp [Raw₀.erase, hs, List.length_eraseKey, hc, hsize, Raw.clearCell]
  | absent =>
    have hcRaw : m.contains a = false := by
      simp [Raw₀.contains, hs]
    have hc : List.containsKey a (m.1.entriesFrom 0).toList = false := by
      rw [← contains_eq_containsKey_entries m h a]
      exact hcRaw
    simp [Raw₀.erase, hs, List.length_eraseKey, hc, hsize]

theorem wfImp_erase [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} {a : α} (h : Raw.WFImp m.1) :
    Raw.WFImp (m.erase a).1 := by
  have hp := toListModel_erase (a := a) h
  have hcache := size_erase_eq_length_eraseKey m h a
  have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
    simpa [toListModel_buckets_eq] using h.size_eq
  refine { cells_pos := ?_, keysValues := ?_, size_eq := ?_, distinct := ?_, size_lt := ?_, reachable := ?_ }
  · simpa [keyArray_size_erase] using m.2
  · exact keysValues_erase m h.keysValues a
  · exact hcache.trans ((by simpa [toListModel_buckets_eq] using hp.length_eq.symm))
  · exact h.distinct.eraseKey.perm hp
  · rw [keyArray_size_erase, hcache]
    have hle := List.length_eraseKey_le
      (l := (m.1.entriesFrom 0).toList) (k := a)
    have hlt := h.size_lt
    omega
  · intro i hi k hkey query hmatch
    cases hs : m.scan a with
    | found index oldKey oldValue hfound =>
      have hi' : i < m.1.keyArray.size := by
        simpa [Raw₀.erase, hs, Raw.clearCell] using hi
      have hkey' : m.1.keyArray[i] = .some k := by
        simpa [Raw₀.erase, hs, Raw.clearCell] using hkey
      simpa [Raw₀.erase, hs, Raw.clearCell] using
        h.reachable i hi' k hkey' query hmatch
    | absent =>
      have hi' : i < m.1.keyArray.size := by simpa [Raw₀.erase, hs] using hi
      have hkey' : m.1.keyArray[i] = .some k := by simpa [Raw₀.erase, hs] using hkey
      simpa [Raw₀.erase, hs] using h.reachable i hi' k hkey' query hmatch

theorem filterMapStep_keyArray_eq {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (_hkv : Raw.KeysValues m.1.keyArray m.1.valueArray)
    (target : Raw₀.FilterMapTarget (γ := γ) m)
    (_htarget : target.1.1.keyArray = m.1.keyArray) (i : Nat)
    (hi : i < m.1.keyArray.size) :
    (Raw₀.filterMapStep f m target i hi).1.1.keyArray = m.1.keyArray := by
  exact (Raw₀.filterMapStep f m target i hi).2.3

theorem filterMapLoop_keyArray_eq {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (_hkv : Raw.KeysValues m.1.keyArray m.1.valueArray)
    (target : Raw₀.FilterMapTarget (γ := γ) m)
    (_htarget : target.1.1.keyArray = m.1.keyArray) (i : Nat) :
    (Raw₀.filterMapLoop f m target i).1.1.keyArray = m.1.keyArray := by
  exact (Raw₀.filterMapLoop f m target i).2.3

theorem filterMap_keyArray_eq {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (_hkv : Raw.KeysValues m.1.keyArray m.1.valueArray) :
    (m.filterMap f).1.keyArray = m.1.keyArray := by
  unfold Raw₀.filterMap
  exact (Raw₀.filterMapLoop f m (Raw₀.filterMapTarget m) 0).2.3

theorem filterMapStep_eq_target_of_key_eq_none {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (target : Raw₀.FilterMapTarget (γ := γ) m) (i : Nat)
    (hi : i < m.1.keyArray.size) (hkey : m.1.keyArray[i] = .none) :
    Raw₀.filterMapStep f m target i hi = target := by
  unfold Raw₀.filterMapStep
  split
  · rfl
  · rename_i k hk
    rw [hkey] at hk
    cases hk

theorem filterMapStep_eq_target_of_value_eq_none {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (target : Raw₀.FilterMapTarget (γ := γ) m) (i : Nat)
    (hi : i < m.1.keyArray.size) (k : α) (hkey : m.1.keyArray[i] = .some k)
    (hiv : i < m.1.valueArray.size) (hvalue : m.1.valueArray[i] = .none) :
    Raw₀.filterMapStep f m target i hi = target := by
  unfold Raw₀.filterMapStep
  split
  · rename_i hk
    rw [hkey] at hk
  · rename_i key hk
    have hkeq : key = k := NOption.some.inj (hk.symm.trans hkey)
    subst key
    simp only
    split
    · rfl
    · rename_i value hv
      rw [hvalue] at hv
      cases hv

theorem filterMapStep_eq_target_of_apply_eq_none {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (target : Raw₀.FilterMapTarget (γ := γ) m) (i : Nat)
    (hi : i < m.1.keyArray.size) (k : α) (hkey : m.1.keyArray[i] = .some k)
    (hiv : i < m.1.valueArray.size) (stored : NSigma β)
    (hvalue : m.1.valueArray[i] = .some stored) (hfst : stored.fst = k)
    (hf : f k (hfst ▸ stored.snd) = none) :
    Raw₀.filterMapStep f m target i hi = target := by
  unfold Raw₀.filterMapStep
  split
  · rename_i hk
    rw [hkey] at hk
  · rename_i key hk
    have hkeq : key = k := NOption.some.inj (hk.symm.trans hkey)
    subst key
    simp only
    split
    · rename_i hv
      rw [hvalue] at hv
    · rename_i value hv
      have hveq : value = stored := NOption.some.inj (hv.symm.trans hvalue)
      subst value
      simp only [hf]

theorem filterMapStep_raw_eq_setValue {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (target : Raw₀.FilterMapTarget (γ := γ) m) (i : Nat)
    (hi : i < m.1.keyArray.size) (k : α) (hkey : m.1.keyArray[i] = .some k)
    (hiv : i < m.1.valueArray.size) (stored : NSigma β)
    (hvalue : m.1.valueArray[i] = .some stored) (hfst : stored.fst = k)
    (value : γ k) (hf : f k (hfst ▸ stored.snd) = some value)
    (hiTarget : i < target.1.1.keyArray.size)
    (htargetKey : target.1.1.keyArray[i] = .some k) :
    (Raw₀.filterMapStep f m target i hi).1.1 =
      target.1.1.setValue (target.1.1.size + 1) i hiTarget k htargetKey value := by
  unfold Raw₀.filterMapStep
  split
  · rename_i hk
    rw [hkey] at hk
    cases hk
  · rename_i key hk
    have hkeq : key = k := NOption.some.inj (hk.symm.trans hkey)
    subst key
    simp only
    split
    · rename_i hv
      rw [hvalue] at hv
      cases hv
    · rename_i value' hv
      have hveq : value' = stored := NOption.some.inj (hv.symm.trans hvalue)
      subst value'
      simp only [hf]

theorem filterMapLoop_entries_perm {γ : α → Type w}
    (f : (a : α) → β a → Option (γ a)) (m : Raw₀ α β)
    (target : Raw₀.FilterMapTarget (γ := γ) m)
    (i : Nat)
    (hempty : ∀ (j : Nat) (hj : j < m.1.keyArray.size), i ≤ j →
      target.1.1.entryAtInBounds? j (by simpa [target.2.1] using hj) = none) :
    let result := Raw₀.filterMapLoop f m target i
    (result.1.1.entriesFrom 0).toList ~
      (target.1.1.entriesFrom 0).toList ++
        (m.1.entriesFrom i).toList.filterMap
          (fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  rw [Raw₀.filterMapLoop.eq_def]
  by_cases hi : i < m.1.keyArray.size
  · rw [dite_eq_left hi]
    rw [Raw.entriesFrom.eq_def (b := m.1) (i := i), dite_eq_left hi]
    cases hkey : m.1.keyArray[i] with
    | none =>
      have he := entryAtInBounds_eq_none_of_key_eq_none m.1 i hi hkey
      rw [he, filterMapStep_eq_target_of_key_eq_none f m target i hi hkey]
      apply filterMapLoop_entries_perm
      intro j hj hij
      exact hempty j hj (by omega)
    | some k =>
      have hiv : i < m.1.valueArray.size := by simpa [m.1.keysValues.1] using hi
      cases hvalue : m.1.valueArray[i] with
      | none =>
        have he := entryAtInBounds_eq_none_of_value_eq_none m.1 i hi hiv hvalue
        rw [he, filterMapStep_eq_target_of_value_eq_none f m target i hi k hkey hiv hvalue]
        apply filterMapLoop_entries_perm
        intro j hj hij
        exact hempty j hj (by omega)
      | some stored =>
        have hcell := m.1.keysValues.2 i hi hiv
        rw [hkey, hvalue] at hcell
        cases hcell
        have he : m.1.entryAtInBounds? i hi = some ⟨stored.fst, stored.snd⟩ := by
          unfold Raw.entryAtInBounds?
          rw [dite_eq_left hiv]
          simp [Raw.cellEntry?, hkey, hvalue]
        rw [he]
        simp only [AssocList.toList_cons, List.filterMap_cons]
        cases hf : f stored.fst stored.snd with
        | none =>
          rw [filterMapStep_eq_target_of_apply_eq_none f m target i hi stored.fst hkey
            hiv stored hvalue rfl hf]
          simp only [Option.map_none]
          apply filterMapLoop_entries_perm
          intro j hj hij
          exact hempty j hj (by omega)
        | some value =>
          let hiTarget : i < target.1.1.keyArray.size := by
            simpa [target.2.1] using hi
          have htargetKey : target.1.1.keyArray[i] = .some stored.fst := by
            simpa [target.2.3] using hkey
          let next := Raw₀.filterMapStep f m target i hi
          change ((Raw₀.filterMapLoop f m next (i + 1)).1.1.entriesFrom 0).toList ~ _
          simp only [Option.map_some]
          have hnextRaw : next.1.1 =
              target.1.1.setValue (target.1.1.size + 1) i hiTarget stored.fst
                htargetKey value := by
            exact filterMapStep_raw_eq_setValue f m target i hi stored.fst hkey hiv stored
              hvalue rfl value hf hiTarget htargetKey
          have hemptyNext : ∀ (j : Nat) (hj : j < m.1.keyArray.size), i + 1 ≤ j →
              next.1.1.entryAtInBounds? j (by simpa [next.2.1] using hj) = none := by
            intro j hj hij
            let hjNext : j < next.1.1.keyArray.size := by simpa [next.2.1] using hj
            let updated := target.1.1.setValue (target.1.1.size + 1) i hiTarget
              stored.fst htargetKey value
            let hjUpdated : j < updated.keyArray.size := by
              simpa [updated, Raw.setValue, target.2.1] using hj
            let inserted := target.1.1.setEntry (target.1.1.size + 1) i hiTarget
              stored.fst value
            let hjInserted : j < inserted.keyArray.size := by
              simpa [inserted, Raw.setEntry, Raw.setCell, target.2.1] using hj
            calc
              next.1.1.entryAtInBounds? j hjNext =
                  updated.entryAtInBounds? j hjUpdated :=
                entryAtInBounds_congr hnextRaw j hjNext hjUpdated
              _ = inserted.entryAtInBounds? j hjInserted := by
                apply entryAtInBounds_congr
                dsimp only [updated, inserted]
                exact (Raw.setEntry_eq_setValue target.1.1 (target.1.1.size + 1) i hiTarget
                  stored.fst htargetKey value).symm
              _ = target.1.1.entryAtInBounds? j (by simpa [target.2.1] using hj) := by
                exact entryAtInBounds_setEntry_ne target.1.1 (target.1.1.size + 1) i j
                  stored.fst value hiTarget hjInserted target.2.2 (by omega)
              _ = none := hempty j hj (by omega)
          have hrec := filterMapLoop_entries_perm f m next (i + 1) hemptyNext
          have hemptyAt : target.1.1.entryAtInBounds? i hiTarget = none :=
            hempty i hi (by omega)
          have hpSet : (next.1.1.entriesFrom 0).toList ~
              ⟨stored.fst, value⟩ :: (target.1.1.entriesFrom 0).toList := by
            rw [hnextRaw]
            rw [← Raw.setEntry_eq_setValue target.1.1 (target.1.1.size + 1) i hiTarget
              stored.fst htargetKey value]
            exact setEntry_empty_perm target.1.1 (target.1.1.size + 1) i hiTarget
              target.2.2 stored.fst value hemptyAt
          refine hrec.trans ?_
          refine (hpSet.append_right _).trans ?_
          simpa [List.cons_append] using
            (List.perm_middle (l₁ := (target.1.1.entriesFrom 0).toList)
              (l₂ := (m.1.entriesFrom (i + 1)).toList.filterMap
                (fun p => (f p.1 p.2).map (⟨p.1, ·⟩)))
              (a := Sigma.mk stored.fst value)).symm
  · rw [dite_eq_right hi]
    rw [Raw.entriesFrom.eq_def (b := m.1) (i := i), dite_eq_right hi]
    simp
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ hi

theorem filterMapLoop_size {gamma : α → Type w}
    (f : (a : α) → β a → Option (gamma a)) (m : Raw₀ α β)
    (target : Raw₀.FilterMapTarget (γ := gamma) m)
    (i : Nat) :
    (Raw₀.filterMapLoop f m target i).1.1.size = target.1.1.size +
      ((m.1.entriesFrom i).toList.filterMap
        (fun p => (f p.1 p.2).map
          (fun x => (⟨p.1, x⟩ : (a : α) × gamma a)))).length := by
  rw [Raw₀.filterMapLoop.eq_def]
  by_cases hi : i < m.1.keyArray.size
  · rw [dite_eq_left hi]
    rw [Raw.entriesFrom.eq_def (b := m.1) (i := i), dite_eq_left hi]
    cases hkey : m.1.keyArray[i] with
    | none =>
      have he := entryAtInBounds_eq_none_of_key_eq_none m.1 i hi hkey
      rw [he, filterMapStep_eq_target_of_key_eq_none f m target i hi hkey]
      exact filterMapLoop_size f m target (i + 1)
    | some k =>
      have hiv : i < m.1.valueArray.size := by simpa [m.1.keysValues.1] using hi
      cases hvalue : m.1.valueArray[i] with
      | none =>
        have he := entryAtInBounds_eq_none_of_value_eq_none m.1 i hi hiv hvalue
        rw [he, filterMapStep_eq_target_of_value_eq_none f m target i hi k hkey hiv hvalue]
        exact filterMapLoop_size f m target (i + 1)
      | some stored =>
        have hcell := m.1.keysValues.2 i hi hiv
        rw [hkey, hvalue] at hcell
        cases hcell
        have he : m.1.entryAtInBounds? i hi = some ⟨stored.fst, stored.snd⟩ := by
          unfold Raw.entryAtInBounds?
          rw [dite_eq_left hiv]
          simp [Raw.cellEntry?, hkey, hvalue]
        rw [he]
        simp only [AssocList.toList_cons, List.filterMap_cons]
        cases hf : f stored.fst stored.snd with
        | none =>
          rw [filterMapStep_eq_target_of_apply_eq_none f m target i hi stored.fst hkey
            hiv stored hvalue rfl hf]
          simp only [Option.map_none]
          exact filterMapLoop_size f m target (i + 1)
        | some value =>
          let hiTarget : i < target.1.1.keyArray.size := by
            simpa [target.2.1] using hi
          have htargetKey : target.1.1.keyArray[i] = .some stored.fst := by
            simpa [target.2.3] using hkey
          let next := Raw₀.filterMapStep f m target i hi
          change (Raw₀.filterMapLoop f m next (i + 1)).1.1.size = _
          simp only [Option.map_some, List.length_cons]
          have hrec := filterMapLoop_size f m next (i + 1)
          rw [hrec]
          have hnextRaw : next.1.1 =
              target.1.1.setValue (target.1.1.size + 1) i hiTarget stored.fst
                htargetKey value := by
            exact filterMapStep_raw_eq_setValue f m target i hi stored.fst hkey hiv stored
              hvalue rfl value hf hiTarget htargetKey
          rw [hnextRaw]
          simp only [Raw.setValue]
          omega
  · rw [dite_eq_right hi]
    rw [Raw.entriesFrom.eq_def (b := m.1) (i := i), dite_eq_right hi]
    simp
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ hi

theorem toListModel_filterMap {γ : α → Type w}
    (m : Raw₀ α β) (f : (a : α) → β a → Option (γ a)) :
    toListModel (m.filterMap f).1.buckets ~
      (toListModel m.1.buckets).filterMap
        (fun p => (f p.1 p.2).map (⟨p.1, ·⟩)) := by
  let target : Raw₀.FilterMapTarget (γ := γ) m :=
    Raw₀.filterMapTarget m
  have hempty : ∀ (j : Nat) (hj : j < m.1.keyArray.size), 0 ≤ j →
      target.1.1.entryAtInBounds? j (by simpa [target.2.1] using hj) = none := by
    intro j hj _
    exact entryAtInBounds_eq_none_of_value_eq_none target.1.1 j
      (by simpa [target.2.1] using hj)
      (by simpa [target, Raw₀.filterMapTarget] using hj)
      (by simp [target, Raw₀.filterMapTarget])
  have hp := filterMapLoop_entries_perm f m target 0 hempty
  rw [Raw₀.filterMap, toListModel_buckets_eq, toListModel_buckets_eq]
  have htarget : target.1.1.entriesFrom 0 = .nil := by
    apply entriesFrom_eq_nil_of_values_none
    intro i hi
    simp [target, Raw₀.filterMapTarget]
  rw [htarget] at hp
  simpa using hp

theorem size_filterMap_eq_length {γ : α → Type w}
    (m : Raw₀ α β) (f : (a : α) → β a → Option (γ a)) :
    (m.filterMap f).1.size =
      ((m.1.entriesFrom 0).toList.filterMap
        (fun p => (f p.1 p.2).map
          (fun x => (⟨p.1, x⟩ : (a : α) × γ a)))).length := by
  let target : Raw₀.FilterMapTarget (γ := γ) m :=
    Raw₀.filterMapTarget m
  have hs := filterMapLoop_size f m target 0
  rw [Raw₀.filterMap]
  simpa [target, Raw₀.filterMapTarget] using hs

@[simp] theorem keyArray_size_filterMap {γ : α → Type w}
    (m : Raw₀ α β) (f : (a : α) → β a → Option (γ a)) :
    (m.filterMap f).1.keyArray.size = m.1.keyArray.size := by
  unfold Raw₀.filterMap
  exact (Raw₀.filterMapLoop f m _ 0).2.1

theorem wfImp_filterMap [BEq α] [Hashable α] [EquivBEq α]
    {γ : α → Type w} {m : Raw₀ α β} (h : Raw.WFImp m.1)
    {f : (a : α) → β a → Option (γ a)} : Raw.WFImp (m.filterMap f).1 := by
  have hp := toListModel_filterMap m f
  have hcache := size_filterMap_eq_length m f
  have hsize : m.1.size = (m.1.entriesFrom 0).toList.length := by
    simpa [toListModel_buckets_eq] using h.size_eq
  have hkeys := filterMap_keyArray_eq f m h.keysValues
  refine { cells_pos := ?_, keysValues := ?_, size_eq := ?_, distinct := ?_, size_lt := ?_, reachable := ?_ }
  · simpa using m.2
  · exact (Raw₀.filterMapLoop f m (Raw₀.filterMapTarget m) 0).2.2
  · exact hcache.trans (by simpa [toListModel_buckets_eq] using hp.length_eq.symm)
  · exact h.distinct.filterMap.perm hp
  · rw [keyArray_size_filterMap, hcache]
    have hle := List.length_filterMap_le
      (fun p => (f p.1 p.2).map
        (fun x => (⟨p.1, x⟩ : (a : α) × γ a)))
      (m.1.entriesFrom 0).toList
    have hlt := h.size_lt
    omega
  · intro i hi k hkey query hmatch
    have hi' : i < m.1.keyArray.size := by simpa only [hkeys] using hi
    have hkey' : m.1.keyArray[i] = .some k := by
      exact ((Array.ext_iff.mp hkeys).2 i hi hi').symm.trans hkey
    have hp := h.reachable i hi' k hkey' query hmatch
    simpa only [hkeys] using hp

theorem toListModel_map {γ : α → Type w}
    (m : Raw₀ α β) (f : (a : α) → β a → γ a) :
    toListModel (m.map f).1.buckets ~
      (toListModel m.1.buckets).map (fun p => ⟨p.1, f p.1 p.2⟩) := by
  simpa [Raw₀.map] using
    (toListModel_filterMap m (fun k v => some (f k v)))

theorem wfImp_map [BEq α] [Hashable α] [EquivBEq α]
    {γ : α → Type w} {m : Raw₀ α β} (h : Raw.WFImp m.1)
    {f : (a : α) → β a → γ a} : Raw.WFImp (m.map f).1 := by
  simpa [Raw₀.map] using
    (wfImp_filterMap (m := m) h (f := fun k v => some (f k v)))

theorem toListModel_filter (m : Raw₀ α β) (f : (a : α) → β a → Bool) :
    toListModel (m.filter f).1.buckets ~
      (toListModel m.1.buckets).filter (fun p => f p.1 p.2) := by
  refine (toListModel_filterMap m
    (fun k v => if f k v then some v else none)).trans (.of_eq ?_)
  induction toListModel m.1.buckets using List.assoc_induction with
  | nil => rfl
  | cons k v l ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    cases f k v <;> simp_all

theorem wfImp_filter [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1)
    {f : (a : α) → β a → Bool} : Raw.WFImp (m.filter f).1 := by
  exact wfImp_filterMap (m := m) h

/-! # Access operations -/

theorem contains_eq_containsKey [BEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.contains a = List.containsKey a (toListModel m.1.buckets) := by
  simpa [toListModel_buckets_eq] using contains_eq_containsKey_entries m hm a

theorem containsₘ_eq_containsKey [BEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.containsₘ a = List.containsKey a (toListModel m.1.buckets) := by
  simpa [Raw₀.containsₘ] using contains_eq_containsKey (m := m) hm (a := a)

theorem get?_eq_getValueCast? [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.get? a = List.getValueCast? a (toListModel m.1.buckets) := by
  simpa [toListModel_buckets_eq] using get?_eq_getValueCast?_entries m hm a

theorem get?ₘ_eq_getValueCast? [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.get?ₘ a = List.getValueCast? a (toListModel m.1.buckets) := by
  simpa [Raw₀.get?ₘ] using get?_eq_getValueCast? (m := m) hm (a := a)

theorem getEntry?_eq_getEntry? [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getEntry? a = List.getEntry? a (toListModel m.1.buckets) := by
  simpa [toListModel_buckets_eq] using getEntry?_eq_getEntry?_entries m hm a

theorem getEntry?ₘ_eq_getEntry? [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getEntry?ₘ a = List.getEntry? a (toListModel m.1.buckets) := by
  simpa [Raw₀.getEntry?ₘ] using getEntry?_eq_getEntry? (m := m) hm (a := a)

private theorem get?_eq_some_get [BEq α] [LawfulBEq α] [Hashable α]
    (m : Raw₀ α β) (a : α) (h : m.contains a) :
    m.get? a = some (m.get a h) := by
  unfold Raw₀.get
  exact (Option.some_get _).symm

private theorem getEntry?_eq_some_getEntry [BEq α] [Hashable α]
    (m : Raw₀ α β) (a : α) (h : m.contains a) :
    m.getEntry? a = some (m.getEntry a h) := by
  unfold Raw₀.getEntry
  exact (Option.some_get _).symm

theorem get_eq_getValueCast [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    m.get a h = List.getValueCast a (toListModel m.1.buckets)
      (contains_eq_containsKey hm ▸ h) := by
  have hs := get?_eq_some_get m a h
  rw [get?_eq_getValueCast? hm,
    List.getValueCast?_eq_some_getValueCast (contains_eq_containsKey hm ▸ h)] at hs
  exact Option.some.inj hs.symm

theorem getₘ_eq_getValue [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {h : m.containsₘ a} :
    m.getₘ a h = List.getValueCast a (toListModel m.1.buckets)
      (containsₘ_eq_containsKey hm ▸ h) := by
  simpa [Raw₀.getₘ, Raw₀.containsₘ] using
    get_eq_getValueCast (m := m) hm (a := a) (h := h)

theorem getEntry_eq_getEntry [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    m.getEntry a h = List.getEntry a (toListModel m.1.buckets)
      (contains_eq_containsKey hm ▸ h) := by
  have hs := getEntry?_eq_some_getEntry m a h
  rw [getEntry?_eq_getEntry? hm,
    List.getEntry?_eq_some_getEntry (contains_eq_containsKey hm ▸ h)] at hs
  exact Option.some.inj hs.symm

theorem getEntryₘ_eq_getEntry [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {h : m.containsₘ a} :
    m.getEntryₘ a h = List.getEntry a (toListModel m.1.buckets)
      (containsₘ_eq_containsKey hm ▸ h) := by
  simpa [Raw₀.getEntryₘ, Raw₀.containsₘ] using
    getEntry_eq_getEntry (m := m) hm (a := a) (h := h)

theorem getEntryD_eq_getEntryD [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α}
    {fallback : (a : α) × β a} :
    m.getEntryD a fallback = List.getEntryD a fallback (toListModel m.1.buckets) := by
  simp only [Raw₀.getEntryD, List.getEntryD_eq_getEntry?, getEntry?_eq_getEntry? hm]

theorem getEntryDₘ_eq_getEntryD [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α}
    {fallback : (a : α) × β a} :
    m.getEntryDₘ a fallback = List.getEntryD a fallback (toListModel m.1.buckets) := by
  simpa [Raw₀.getEntryDₘ] using getEntryD_eq_getEntryD (m := m) hm

theorem getEntry!_eq_getEntry! [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α}
    [Inhabited ((a : α) × β a)] :
    m.getEntry! a = List.getEntry! a (toListModel m.1.buckets) := by
  simp only [Raw₀.getEntry!, List.getEntry!_eq_getEntry?, getEntry?_eq_getEntry? hm,
    Option.get!_eq_getD]

theorem getEntry!ₘ_eq_getEntry! [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α}
    [Inhabited ((a : α) × β a)] :
    m.getEntry!ₘ a = List.getEntry! a (toListModel m.1.buckets) := by
  simpa [Raw₀.getEntry!ₘ] using getEntry!_eq_getEntry! (m := m) hm (a := a)

theorem getD_eq_getValueCastD [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {fallback : β a} :
    m.getD a fallback = List.getValueCastD a (toListModel m.1.buckets) fallback := by
  simp only [Raw₀.getD, List.getValueCastD_eq_getValueCast?, get?_eq_getValueCast? hm]

theorem getDₘ_eq_getValueCastD [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {fallback : β a} :
    m.getDₘ a fallback = List.getValueCastD a (toListModel m.1.buckets) fallback := by
  simpa [Raw₀.getDₘ] using getD_eq_getValueCastD (m := m) hm

theorem get!_eq_getValueCast! [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} [Inhabited (β a)] :
    m.get! a = List.getValueCast! a (toListModel m.1.buckets) := by
  rw [Raw₀.get!, get?_eq_getValueCast? hm, List.getValueCast!_eq_getValueCast?]
  cases hopt : List.getValueCast? a (toListModel m.1.buckets) <;>
    simp [Option.get!, panicWithPosWithDecl, panic, panicCore]

theorem get!ₘ_eq_getValueCast! [BEq α] [LawfulBEq α] [Hashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} [Inhabited (β a)] :
    m.get!ₘ a = List.getValueCast! a (toListModel m.1.buckets) := by
  simpa [Raw₀.get!ₘ] using get!_eq_getValueCast! (m := m) hm (a := a)

private theorem getKey?_eq_map_getEntry? [BEq α] [Hashable α]
    (m : Raw₀ α β) (a : α) :
    m.getKey? a = (m.getEntry? a).map (fun p => p.1) := by
  unfold Raw₀.getKey? Raw₀.getEntry?
  cases m.scan a <;> rfl

theorem getKey?_eq_getKey? [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getKey? a = List.getKey? a (toListModel m.1.buckets) := by
  rw [getKey?_eq_map_getEntry?, getEntry?_eq_getEntry? hm,
    List.getKey?_eq_getEntry?]

theorem getKey?ₘ_eq_getKey? [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getKey?ₘ a = List.getKey? a (toListModel m.1.buckets) := by
  simpa [Raw₀.getKey?ₘ] using getKey?_eq_getKey? (m := m) hm (a := a)

private theorem getKey?_eq_some_getKey [BEq α] [Hashable α]
    (m : Raw₀ α β) (a : α) (h : m.contains a) :
    m.getKey? a = some (m.getKey a h) := by
  unfold Raw₀.getKey
  exact (Option.some_get _).symm

theorem getKey_eq_getKey [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    m.getKey a h = List.getKey a (toListModel m.1.buckets)
      (contains_eq_containsKey hm ▸ h) := by
  have hs := getKey?_eq_some_getKey m a h
  rw [getKey?_eq_getKey? hm,
    List.getKey?_eq_some_getKey (contains_eq_containsKey hm ▸ h)] at hs
  exact Option.some.inj hs.symm

theorem getKeyₘ_eq_getKey [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    m.getKeyₘ a h = List.getKey a (toListModel m.1.buckets)
      (contains_eq_containsKey hm ▸ h) := by
  simpa [Raw₀.getKeyₘ] using getKey_eq_getKey (m := m) hm (a := a) (h := h)

theorem getKeyD_eq_getKeyD [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a fallback : α} :
    m.getKeyD a fallback = List.getKeyD a (toListModel m.1.buckets) fallback := by
  simp only [Raw₀.getKeyD, List.getKeyD_eq_getKey?, getKey?_eq_getKey? hm]

theorem getKeyDₘ_eq_getKeyD [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a fallback : α} :
    m.getKeyDₘ a fallback = List.getKeyD a (toListModel m.1.buckets) fallback := by
  simpa [Raw₀.getKeyDₘ] using getKeyD_eq_getKeyD (m := m) hm

theorem getKey!_eq_getKey! [BEq α] [Hashable α] [EquivBEq α] [Inhabited α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getKey! a = List.getKey! a (toListModel m.1.buckets) := by
  rw [Raw₀.getKey!, getKey?_eq_getKey? hm, List.getKey!_eq_getKey?]
  cases hopt : List.getKey? a (toListModel m.1.buckets) <;>
    simp [Option.get!, panicWithPosWithDecl, panic, panicCore]

theorem getKey!ₘ_eq_getKey! [BEq α] [Hashable α] [EquivBEq α] [Inhabited α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} :
    m.getKey!ₘ a = List.getKey! a (toListModel m.1.buckets) := by
  simpa [Raw₀.getKey!ₘ] using getKey!_eq_getKey! (m := m) hm (a := a)

namespace Raw₀.Const

variable {beta : Type v}

private theorem get?_eq_map_getEntry? [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => beta)) (a : α) :
    Raw₀.Const.get? m a = (m.getEntry? a).map (fun p => p.2) := by
  unfold Raw₀.Const.get? Raw₀.getEntry?
  cases m.scan a <;> rfl

theorem get?_eq_getValue? [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} :
    Raw₀.Const.get? m a = List.getValue? a (toListModel m.1.buckets) := by
  rw [get?_eq_map_getEntry?, Std.DHashMap.Internal.getEntry?_eq_getEntry? hm,
    List.getValue?_eq_getEntry?]

theorem get?ₘ_eq_getValue? [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} :
    Raw₀.Const.get?ₘ m a = List.getValue? a (toListModel m.1.buckets) := by
  simpa [Raw₀.Const.get?ₘ] using get?_eq_getValue? (m := m) hm (a := a)

private theorem get?_eq_some_get [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => beta)) (a : α) (h : m.contains a) :
    Raw₀.Const.get? m a = some (Raw₀.Const.get m a h) := by
  unfold Raw₀.Const.get
  exact (Option.some_get _).symm

theorem get_eq_getValue [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} {h : m.contains a} :
    Raw₀.Const.get m a h = List.getValue a (toListModel m.1.buckets)
      (Std.DHashMap.Internal.contains_eq_containsKey hm ▸ h) := by
  have hs := get?_eq_some_get m a h
  rw [get?_eq_getValue? hm,
    List.getValue?_eq_some_getValue
      (Std.DHashMap.Internal.contains_eq_containsKey hm ▸ h)] at hs
  exact Option.some.inj hs.symm

theorem getₘ_eq_getValue [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} {h : m.containsₘ a} :
    Raw₀.Const.getₘ m a h = List.getValue a (toListModel m.1.buckets)
      (Std.DHashMap.Internal.containsₘ_eq_containsKey hm ▸ h) := by
  simpa [Raw₀.Const.getₘ, Raw₀.containsₘ] using
    get_eq_getValue (m := m) hm (a := a) (h := h)

theorem getD_eq_getValueD [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} {fallback : beta} :
    Raw₀.Const.getD m a fallback = List.getValueD a (toListModel m.1.buckets) fallback := by
  simp only [Raw₀.Const.getD, List.getValueD_eq_getValue?, get?_eq_getValue? hm]

theorem getDₘ_eq_getValueD [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} {fallback : beta} :
    Raw₀.Const.getDₘ m a fallback = List.getValueD a (toListModel m.1.buckets) fallback := by
  simpa [Raw₀.Const.getDₘ] using getD_eq_getValueD (m := m) hm

theorem get!_eq_getValue! [BEq α] [Hashable α] [EquivBEq α] [Inhabited beta]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} :
    Raw₀.Const.get! m a = List.getValue! a (toListModel m.1.buckets) := by
  rw [Raw₀.Const.get!, get?_eq_getValue? hm, List.getValue!_eq_getValue?]
  cases hopt : List.getValue? a (toListModel m.1.buckets) <;>
    simp [Option.get!, panicWithPosWithDecl, panic, panicCore]

theorem get!ₘ_eq_getValue! [BEq α] [Hashable α] [EquivBEq α] [Inhabited beta]
    {m : Raw₀ α (fun _ => beta)} (hm : Raw.WFImp m.1) {a : α} :
    Raw₀.Const.get!ₘ m a = List.getValue! a (toListModel m.1.buckets) := by
  simpa [Raw₀.Const.get!ₘ] using get!_eq_getValue! (m := m) hm (a := a)

end Raw₀.Const

theorem Raw₀.wfImp_modify [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {f : β a → β a} :
    Raw.WFImp (m.modify a f).1 := by
  unfold Raw₀.modify
  split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h

theorem Raw₀.wfImp_alter [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α}
    {f : Option (β a) → Option (β a)} : Raw.WFImp (m.alter a f).1 := by
  unfold Raw₀.alter
  split <;> split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h |
    exact Std.DHashMap.Internal.wfImp_erase h

theorem Raw₀.Const.wfImp_modify {beta : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α} {f : beta → beta} :
    Raw.WFImp (Raw₀.Const.modify m a f).1 := by
  unfold Raw₀.Const.modify
  split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h

theorem Raw₀.Const.wfImp_alter {beta : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α}
    {f : Option beta → Option beta} : Raw.WFImp (Raw₀.Const.alter m a f).1 := by
  unfold Raw₀.Const.alter
  split <;> split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h |
    exact Std.DHashMap.Internal.wfImp_erase h

/-! # Bulk operations -/

private theorem wfImp_insertIfNew_early [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.insertIfNew a b).1 := by
  unfold Raw₀.insertIfNew
  split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h

private theorem toListModel_insertIfNew_early [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    toListModel (m.insertIfNew a b).1.buckets ~
      List.insertEntryIfNew a b (toListModel m.1.buckets) := by
  rw [Raw₀.insertIfNew, List.insertEntryIfNew, contains_eq_containsKey h]
  split
  · exact .rfl
  · rename_i hn
    have hc : List.containsKey a (toListModel m.1.buckets) = false :=
      Bool.not_eq_true _ ▸ hn
    simpa [List.insertEntry_of_containsKey_eq_false hc] using
      (toListModel_insert (m := m) h (a := a) (b := b))

theorem toListModel_insertListₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.insertListₘ m l).1.buckets ~
      List.insertList (toListModel m.1.buckets) l := by
  induction l using List.assoc_induction generalizing m with
  | nil =>
    rw [Raw₀.insertListₘ, List.foldl_nil, List.insertList.eq_def]
  | cons k v tl ih =>
    rw [Raw₀.insertListₘ, List.foldl_cons, List.insertList.eq_def]
    apply (ih (wfImp_insert h)).trans
    exact List.insertList_perm_of_perm_first (toListModel_insert h) (wfImp_insert h).distinct

theorem toListModel_eraseListₘ [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} {l : List α} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.eraseListₘ m l).1.buckets ~
      List.eraseList (toListModel m.1.buckets) l := by
  induction l generalizing m with
  | nil =>
    rw [Raw₀.eraseListₘ, List.foldl_nil, List.eraseList.eq_def]
  | cons hd tl ih =>
    rw [Raw₀.eraseListₘ, List.foldl_cons, List.eraseList.eq_def]
    apply (ih (wfImp_erase h)).trans
    exact List.eraseList_perm_of_perm_first (toListModel_erase h) (wfImp_erase h).distinct

theorem toListModel_insertListIfNewₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.insertListIfNewₘ m l).1.buckets ~
      List.insertListIfNew (toListModel m.1.buckets) l := by
  induction l using List.assoc_induction generalizing m with
  | nil =>
    rw [Raw₀.insertListIfNewₘ, List.foldl_nil, List.insertListIfNew.eq_def]
  | cons k v tl ih =>
    rw [Raw₀.insertListIfNewₘ, List.foldl_cons, List.insertListIfNew.eq_def]
    apply (ih (wfImp_insertIfNew_early h)).trans
    exact List.insertListIfNew_perm_of_perm_first
      (toListModel_insertIfNew_early h) (wfImp_insertIfNew_early h).distinct

theorem toListModel_insertMany_list [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.insertMany m l).1.1.buckets ~
      List.insertList (toListModel m.1.buckets) l := by
  rw [Raw₀.insertMany_eq_insertListₘ]
  exact toListModel_insertListₘ h

theorem toListModel_insertManyIfNew_list [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.insertManyIfNew m l).1.1.buckets ~
      List.insertListIfNew (toListModel m.1.buckets) l := by
  rw [Raw₀.insertManyIfNew_eq_insertListIfNewₘ]
  exact toListModel_insertListIfNewₘ h

theorem Raw₀.insertMany_array_eq_insertMany_toList [BEq α] [Hashable α]
    (m : Raw₀ α β) (a : Array ((k : α) × β k)) :
    insertMany m a = insertMany m a.toList := by
  simp only [insertMany, bind_pure, ← Array.forIn_toList,
    forIn_pure_yield_eq_foldl, Array.foldl_toList, Id.run_pure]

theorem Raw₀.Const.insertMany_array_eq_insertMany_toList [BEq α] [Hashable α]
    {beta : Type v} (m : Raw₀ α (fun _ => beta)) (a : Array (α × beta)) :
    Const.insertMany m a = Const.insertMany m a.toList := by
  simp only [Const.insertMany, bind_pure, ← Array.forIn_toList,
    forIn_pure_yield_eq_foldl, Array.foldl_toList, Id.run_pure]

theorem Raw₀.Const.insertManyIfNewUnit_array_eq_insertManyIfNewUnit_toList
    [BEq α] [Hashable α] (m : Raw₀ α (fun _ => Unit)) (a : Array α) :
    Const.insertManyIfNewUnit m a = Const.insertManyIfNewUnit m a.toList := by
  simp only [Const.insertManyIfNewUnit, bind_pure, ← Array.forIn_toList,
    forIn_pure_yield_eq_foldl, Array.foldl_toList, Id.run_pure]

theorem Raw₀.wfImp_insertMany [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {rho : Type w} [ForIn Id rho ((a : α) × β a)] {m : Raw₀ α β} {l : rho}
    (h : Raw.WFImp m.1) : Raw.WFImp (m.insertMany l).1.1 :=
  (m.insertMany l).2 (fun m => Raw.WFImp m.1) (fun h => wfImp_insert h) h

theorem Raw₀.wfImp_insertManyIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {rho : Type w} [ForIn Id rho ((a : α) × β a)] {m : Raw₀ α β} {l : rho}
    (h : Raw.WFImp m.1) : Raw.WFImp (m.insertManyIfNew l).1.1 :=
  (m.insertManyIfNew l).2
    (fun m => Raw.WFImp m.1) (fun h => wfImp_insertIfNew_early h) h

theorem Raw₀.wf_insertMany₀ [BEq α] [Hashable α]
    {rho : Type w} [ForIn Id rho ((a : α) × β a)] {m : Raw α β}
    {h : 0 < m.keyArray.size} {l : rho} (hm : m.WF) :
    (Raw₀.insertMany ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.insertMany ⟨m, h⟩ l).2 (fun m => m.1.WF) (fun h => .insert₀ h) hm

theorem Raw₀.wf_insertManyIfNew₀ [BEq α] [Hashable α]
    {rho : Type w} [ForIn Id rho ((a : α) × β a)] {m : Raw α β}
    {h : 0 < m.keyArray.size} {l : rho} (hm : m.WF) :
    (Raw₀.insertManyIfNew ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.insertManyIfNew ⟨m, h⟩ l).2
    (fun m => m.1.WF) (fun h => .insertIfNew₀ h) hm

/-! # Conditional insertion -/

theorem toListModel_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    toListModel (m.insertIfNew a b).1.buckets ~
      List.insertEntryIfNew a b (toListModel m.1.buckets) := by
  rw [Raw₀.insertIfNew, List.insertEntryIfNew, contains_eq_containsKey h]
  split
  · exact .rfl
  · rename_i hn
    have hc : List.containsKey a (toListModel m.1.buckets) = false :=
      Bool.not_eq_true _ ▸ hn
    simpa [List.insertEntry_of_containsKey_eq_false hc] using
      (toListModel_insert (m := m) h (a := a) (b := b))

theorem wfImp_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.insertIfNew a b).1 := by
  unfold Raw₀.insertIfNew
  split <;> first | exact h | exact wfImp_insert h

theorem wfImp_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.containsThenInsert a b).2.1 := by
  simpa [Raw₀.containsThenInsert] using wfImp_insert (m := m) h (a := a) (b := b)

theorem wfImp_containsThenInsertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.containsThenInsertIfNew a b).2.1 := by
  unfold Raw₀.containsThenInsertIfNew
  split <;> first | exact h | exact wfImp_insert h

theorem wfImp_getThenInsertIfNew? [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.getThenInsertIfNew? a b).2.1 := by
  simpa [Raw₀.getThenInsertIfNew?] using wfImp_insertIfNew (m := m) h (a := a) (b := b)

theorem Raw₀.Const.wfImp_getThenInsertIfNew? {beta : Type v}
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α} {b : beta} :
    Raw.WFImp (Raw₀.Const.getThenInsertIfNew? m a b).2.1 := by
  simpa [Raw₀.Const.getThenInsertIfNew?] using
    wfImp_insertIfNew (m := m) h (a := a) (b := b)

/-! # Names used by the inductive well-formedness interface -/

theorem Raw₀.wfImp_emptyWithCapacity [BEq α] [Hashable α] {c : Nat} :
    Raw.WFImp (Raw₀.emptyWithCapacity c : Raw₀ α β).1 :=
  Std.DHashMap.Internal.wfImp_emptyWithCapacity

theorem Raw₀.wfImp_insert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.insert a b).1 := Std.DHashMap.Internal.wfImp_insert h

theorem Raw₀.wfImp_erase [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} : Raw.WFImp (m.erase a).1 :=
  Std.DHashMap.Internal.wfImp_erase h

theorem Raw₀.wfImp_insertIfNew [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.insertIfNew a b).1 := Std.DHashMap.Internal.wfImp_insertIfNew h

theorem Raw₀.wfImp_containsThenInsert [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.containsThenInsert a b).2.1 :=
  Std.DHashMap.Internal.wfImp_containsThenInsert h

theorem Raw₀.wfImp_containsThenInsertIfNew [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.containsThenInsertIfNew a b).2.1 :=
  Std.DHashMap.Internal.wfImp_containsThenInsertIfNew h

theorem Raw₀.wfImp_getThenInsertIfNew? [BEq α] [LawfulBEq α] [Hashable α]
    [EquivBEq α] {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {b : β a} :
    Raw.WFImp (m.getThenInsertIfNew? a b).2.1 :=
  Std.DHashMap.Internal.wfImp_getThenInsertIfNew? h

theorem Raw₀.wfImp_filter [BEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {f : (a : α) → β a → Bool} :
    Raw.WFImp (m.filter f).1 := Std.DHashMap.Internal.wfImp_filter h

/-! # Update operations -/

theorem toListModel_alter [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α}
    {f : Option (β a) → Option (β a)} :
    toListModel (m.alter a f).1.buckets ~
      List.alterKey a f (toListModel m.1.buckets) := by
  rw [Raw₀.alter, get?_eq_getValueCast? h]
  cases ho : List.getValueCast? a (toListModel m.1.buckets) with
  | none =>
    have hc : List.containsKey a (toListModel m.1.buckets) = false := by
      simp [List.containsKey_eq_isSome_getValueCast?, ho]
    cases hf : f none with
    | none => simp [List.alterKey, ho, hf, List.eraseKey_of_containsKey_eq_false hc]
    | some v =>
      simpa [List.alterKey, ho, hf] using (toListModel_insert (m := m) h (a := a) (b := v))
  | some v =>
    cases hf : f (some v) with
    | none =>
      simpa [List.alterKey, ho, hf] using (toListModel_erase (m := m) h (a := a))
    | some v' =>
      simpa [List.alterKey, ho, hf] using (toListModel_insert (m := m) h (a := a) (b := v'))

theorem wfImp_alter [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α}
    {f : Option (β a) → Option (β a)} : Raw.WFImp (m.alter a f).1 := by
  unfold Raw₀.alter
  split <;> split <;> first | exact h | exact wfImp_insert h | exact wfImp_erase h

theorem toListModel_modify [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {f : β a → β a} :
    toListModel (m.modify a f).1.buckets ~
      List.modifyKey a f (toListModel m.1.buckets) := by
  rw [Raw₀.modify, get?_eq_getValueCast? h]
  cases ho : List.getValueCast? a (toListModel m.1.buckets) with
  | none => simp [List.modifyKey, ho]
  | some v =>
    have hc : List.containsKey a (toListModel m.1.buckets) := by
      simp [List.containsKey_eq_isSome_getValueCast?, ho]
    refine (toListModel_insert (m := m) h (a := a) (b := f v)).trans ?_
    simpa [List.modifyKey, ho] using
      List.Perm.of_eq (List.insertEntry_of_containsKey (v := f v) hc)

theorem wfImp_modify [BEq α] [LawfulBEq α] [Hashable α] [EquivBEq α]
    {m : Raw₀ α β} (h : Raw.WFImp m.1) {a : α} {f : β a → β a} :
    Raw.WFImp (m.modify a f).1 := by
  unfold Raw₀.modify
  split <;> first | exact h | exact wfImp_insert h

namespace Raw₀.Const

variable {beta : Type v}

theorem toListModel_alter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α}
    {f : Option beta → Option beta} :
    toListModel (Raw₀.Const.alter m a f).1.buckets ~
      List.Const.alterKey a f (toListModel m.1.buckets) := by
  rw [Raw₀.Const.alter, get?_eq_getValue? h]
  cases ho : List.getValue? a (toListModel m.1.buckets) with
  | none =>
    have hc : List.containsKey a (toListModel m.1.buckets) = false := by
      simp [List.containsKey_eq_isSome_getValue?, ho]
    cases hf : f none with
    | none => simp [List.Const.alterKey, ho, hf, List.eraseKey_of_containsKey_eq_false hc]
    | some v =>
      simpa [List.Const.alterKey, ho, hf] using
        (Std.DHashMap.Internal.toListModel_insert (m := m) h (a := a) (b := v))
  | some v =>
    cases hf : f (some v) with
    | none =>
      simpa [List.Const.alterKey, ho, hf] using
        (Std.DHashMap.Internal.toListModel_erase (m := m) h (a := a))
    | some v' =>
      simpa [List.Const.alterKey, ho, hf] using
        (Std.DHashMap.Internal.toListModel_insert (m := m) h (a := a) (b := v'))

private theorem wfImp_alter_impl [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α}
    {f : Option beta → Option beta} : Raw.WFImp (Raw₀.Const.alter m a f).1 := by
  unfold Raw₀.Const.alter
  split <;> split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h |
    exact Std.DHashMap.Internal.wfImp_erase h

theorem toListModel_modify [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α} {f : beta → beta} :
    toListModel (Raw₀.Const.modify m a f).1.buckets ~
      List.Const.modifyKey a f (toListModel m.1.buckets) := by
  rw [Raw₀.Const.modify, get?_eq_getValue? h]
  cases ho : List.getValue? a (toListModel m.1.buckets) with
  | none => simp [List.Const.modifyKey, ho]
  | some v =>
    have hc : List.containsKey a (toListModel m.1.buckets) := by
      simp [List.containsKey_eq_isSome_getValue?, ho]
    refine (Std.DHashMap.Internal.toListModel_insert
      (m := m) h (a := a) (b := f v)).trans ?_
    simpa [List.Const.modifyKey, ho] using
      List.Perm.of_eq (List.insertEntry_of_containsKey (v := f v) hc)

private theorem wfImp_modify_impl [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} (h : Raw.WFImp m.1) {a : α} {f : beta → beta} :
    Raw.WFImp (Raw₀.Const.modify m a f).1 := by
  unfold Raw₀.Const.modify
  split <;> first | exact h | exact Std.DHashMap.Internal.wfImp_insert h

end Raw₀.Const

namespace Raw₀.Const

variable {beta : Type v}

theorem toListModel_insertListₘ [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} {l : List (α × beta)} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.Const.insertListₘ m l).1.buckets ~
      List.insertListConst (toListModel m.1.buckets) l := by
  induction l generalizing m with
  | nil =>
    change toListModel m.1.buckets ~ toListModel m.1.buckets
    exact .rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    change toListModel (Raw₀.Const.insertListₘ (m.insert k v) tl).1.buckets ~
      List.insertListConst (List.insertEntry k v (toListModel m.1.buckets)) tl
    apply (ih (Std.DHashMap.Internal.wfImp_insert h)).trans
    exact List.insertList_perm_of_perm_first
      (Std.DHashMap.Internal.toListModel_insert h)
      (Std.DHashMap.Internal.wfImp_insert h).distinct

theorem toListModel_insertMany_list [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Raw₀ α (fun _ => beta)} {l : List (α × beta)} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.Const.insertMany m l).1.1.buckets ~
      List.insertListConst (toListModel m.1.buckets) l := by
  rw [Raw₀.Const.insertMany_eq_insertListₘ]
  exact toListModel_insertListₘ h

theorem toListModel_insertListIfNewUnitₘ [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α (fun _ => Unit)} {l : List α} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.Const.insertListIfNewUnitₘ m l).1.buckets ~
      List.insertListIfNewUnit (toListModel m.1.buckets) l := by
  induction l generalizing m with
  | nil =>
    change toListModel m.1.buckets ~ toListModel m.1.buckets
    exact .rfl
  | cons hd tl ih =>
    change toListModel (Raw₀.Const.insertListIfNewUnitₘ (m.insertIfNew hd ()) tl).1.buckets ~
      List.insertListIfNewUnit
        (List.insertEntryIfNew hd () (toListModel m.1.buckets)) tl
    apply (ih (Std.DHashMap.Internal.wfImp_insertIfNew h)).trans
    exact List.insertListIfNewUnit_perm_of_perm_first
      (Std.DHashMap.Internal.toListModel_insertIfNew h)
      (Std.DHashMap.Internal.wfImp_insertIfNew h).distinct

theorem toListModel_insertManyIfNewUnit_list [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α]
    {m : Raw₀ α (fun _ => Unit)} {l : List α} (h : Raw.WFImp m.1) :
    toListModel (Raw₀.Const.insertManyIfNewUnit m l).1.1.buckets ~
      List.insertListIfNewUnit (toListModel m.1.buckets) l := by
  rw [Raw₀.Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ]
  exact toListModel_insertListIfNewUnitₘ h

theorem wfImp_insertMany [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {rho : Type w} [ForIn Id rho (α × beta)] {m : Raw₀ α (fun _ => beta)} {l : rho}
    (h : Raw.WFImp m.1) : Raw.WFImp (Raw₀.Const.insertMany m l).1.1 :=
  (Raw₀.Const.insertMany m l).2 (fun m => Raw.WFImp m.1)
    (fun h => Std.DHashMap.Internal.wfImp_insert h) h

theorem wf_insertMany₀ [BEq α] [Hashable α]
    {rho : Type w} [ForIn Id rho (α × beta)] {m : Raw α (fun _ => beta)}
    {h : 0 < m.keyArray.size} {l : rho} (hm : m.WF) :
    (Raw₀.Const.insertMany ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.Const.insertMany ⟨m, h⟩ l).2 (fun m => m.1.WF) (fun h => .insert₀ h) hm

theorem wfImp_insertManyIfNewUnit [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {rho : Type w} [ForIn Id rho α] {m : Raw₀ α (fun _ => Unit)} {l : rho}
    (h : Raw.WFImp m.1) : Raw.WFImp (Raw₀.Const.insertManyIfNewUnit m l).1.1 :=
  (Raw₀.Const.insertManyIfNewUnit m l).2 (fun m => Raw.WFImp m.1)
    (fun h => Std.DHashMap.Internal.wfImp_insertIfNew h) h

theorem wf_insertManyIfNewUnit₀ [BEq α] [Hashable α]
    {rho : Type w} [ForIn Id rho α] {m : Raw α (fun _ => Unit)}
    {h : 0 < m.keyArray.size} {l : rho} (hm : m.WF) :
    (Raw₀.Const.insertManyIfNewUnit ⟨m, h⟩ l).1.1.WF :=
  (Raw₀.Const.insertManyIfNewUnit ⟨m, h⟩ l).2
    (fun m => m.1.WF) (fun h => .insertIfNew₀ h) hm

end Raw₀.Const

theorem beq_eq_beqModel [BEq α] [LawfulBEq α] [Hashable α]
    [∀ k, BEq (β k)] {m₁ m₂ : Raw₀ α β}
    (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    Raw₀.beq m₁ m₂ =
      List.beqModel (toListModel m₁.1.buckets) (toListModel m₂.1.buckets) := by
  simp [Raw₀.beq, List.beqModel, Raw.size_eq_length h₁, Raw.size_eq_length h₂,
    Raw.all_eq_all_toListModel, get?_eq_getValueCast? h₂]

theorem Raw₀.Const.beq_eq_beqModel {beta : Type v} [BEq α] [Hashable α] [EquivBEq α]
    [BEq beta]
    {m₁ m₂ : Raw₀ α (fun _ => beta)} (h₁ : Raw.WFImp m₁.1)
    (h₂ : Raw.WFImp m₂.1) :
    Raw₀.Const.beq m₁ m₂ =
      List.Const.beqModel (toListModel m₁.1.buckets) (toListModel m₂.1.buckets) := by
  simp [Raw₀.Const.beq, List.Const.beqModel, Raw.size_eq_length h₁,
    Raw.size_eq_length h₂, Raw.all_eq_all_toListModel,
    Raw₀.Const.get?_eq_getValue? h₂]

theorem insertMany_eq_insertListₘ_toListModel [BEq α] [Hashable α]
    (m m₂ : Raw₀ α β) :
    Raw₀.insertMany m m₂.1 = Raw₀.insertListₘ m (toListModel m₂.1.buckets) := by
  simp only [Raw₀.insertMany, bind_pure]
  simp only [ForIn.forIn]
  simp only [Raw.forIn_eq_forIn_toListModel, forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize toListModel m₂.1.buckets = l
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α} {b : β a}, P m'' → P (m''.insert a b)) →
        P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.1.insert p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).1 =
        Raw₀.insertListₘ t.1 l from this _
  intro t
  induction l generalizing m with
  | nil => simp [Raw₀.insertListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, Raw₀.insertListₘ]
    apply ih

theorem insertManyIfNew_eq_insertListIfNewₘ_toListModel [BEq α] [Hashable α]
    (m m₂ : Raw₀ α β) :
    Raw₀.insertManyIfNew m m₂.1 =
      Raw₀.insertListIfNewₘ m (toListModel m₂.1.buckets) := by
  simp only [Raw₀.insertManyIfNew, bind_pure]
  simp only [ForIn.forIn]
  simp only [Raw.forIn_eq_forIn_toListModel, forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize toListModel m₂.1.buckets = l
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α} {b : β a},
        P m'' → P (m''.insertIfNew a b)) → P m → P m' }),
      (List.foldl (fun m' p =>
        ⟨m'.1.insertIfNew p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).1 =
        Raw₀.insertListIfNewₘ t.1 l from this _
  intro t
  induction l generalizing m with
  | nil => simp [Raw₀.insertListIfNewₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, Raw₀.insertListIfNewₘ]
    apply ih

theorem toListModel_union [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw₀ α β} (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    toListModel (m₁.union m₂).1.buckets ~
      List.insertList (toListModel m₁.1.buckets) (toListModel m₂.1.buckets) := by
  refine List.Perm.trans ?_
    (List.Perm.symm (List.insertList_perm_insertSmallerList h₁.distinct h₂.distinct))
  rw [Raw₀.union, List.insertSmallerList, h₁.size_eq, h₂.size_eq]
  split
  · rw [insertManyIfNew_eq_insertListIfNewₘ_toListModel]
    exact toListModel_insertListIfNewₘ h₂
  · rw [insertMany_eq_insertListₘ_toListModel]
    exact toListModel_insertListₘ h₁

theorem Raw₀.wf_union₀ [BEq α] [Hashable α]
    {m₁ m₂ : Raw α β} {h₁ : 0 < m₁.keyArray.size} {h₂ : 0 < m₂.keyArray.size}
    (hm₁ : m₁.WF) (hm₂ : m₂.WF) :
    (Raw₀.union ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1.WF := by
  unfold Raw₀.union
  split
  · exact (Raw₀.insertManyIfNew ⟨m₂, h₂⟩ m₁).2
      (fun m => m.1.WF) (fun h => .insertIfNew₀ h) hm₂
  · exact (Raw₀.insertMany ⟨m₁, h₁⟩ m₂).2
      (fun m => m.1.WF) (fun h => .insert₀ h) hm₁

theorem wfImp_interSmaller [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ : Raw₀ α β) (m₂ : Raw α β) :
    Raw.WFImp (Raw₀.interSmaller m₁ m₂).1 := by
  unfold Raw₀.interSmaller
  apply @Raw.fold_induction _ β _
    (fun sofar k _ => Raw₀.interSmallerFn m₁ sofar k)
    Raw₀.emptyWithCapacity m₂ (Raw.WFImp ·.1) wfImp_emptyWithCapacity
  intro acc k v hacc
  unfold Raw₀.interSmallerFn
  split
  · exact wfImp_insert hacc
  · exact hacc

theorem toListModel_interSmallerFn [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m sofar : Raw₀ α β) (l : List ((a : α) × β a))
    (hm : Raw.WFImp m.1) (hs : Raw.WFImp sofar.1) (k : α)
    (hml : toListModel sofar.1.buckets ~ l) :
    toListModel (Raw₀.interSmallerFn m sofar k).1.buckets ~
      List.interSmallerFn (toListModel m.1.buckets) l k := by
  unfold Raw₀.interSmallerFn List.interSmallerFn
  rw [getEntry?_eq_getEntry? hm]
  cases hentry : List.getEntry? k (toListModel m.1.buckets) with
  | none =>
    change toListModel sofar.1.buckets ~ l
    exact hml
  | some entry =>
    rcases entry with ⟨key, value⟩
    change toListModel (sofar.insert key value).1.buckets ~ List.insertEntry key value l
    exact (toListModel_insert hs).trans
      (List.insertEntry_of_perm hs.distinct hml)

theorem toListModel_interSmaller [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m₁ : Raw₀ α β) (m₂ : Raw α β)
    (hm₁ : Raw.WFImp m₁.1) :
    toListModel (Raw₀.interSmaller m₁ m₂).1.buckets ~
      List.interSmaller (toListModel m₁.1.buckets) (toListModel m₂.buckets) := by
  unfold Raw₀.interSmaller
  rw [Raw.fold_eq_foldl_toListModel, List.interSmaller]
  generalize toListModel m₂.buckets = entries
  suffices ∀ acc accEntries,
      Raw.WFImp acc.1 → toListModel acc.1.buckets ~ accEntries →
        toListModel
            (entries.foldl (fun acc p => Raw₀.interSmallerFn m₁ acc p.1) acc).1.buckets ~
          entries.foldl
            (fun accEntries p =>
              List.interSmallerFn (toListModel m₁.1.buckets) accEntries p.1)
            accEntries from
    this Raw₀.emptyWithCapacity [] wfImp_emptyWithCapacity
      (by rw [toListModel_buckets_emptyWithCapacity])
  intro acc accEntries hacc hperm
  induction entries using List.assoc_induction generalizing acc accEntries with
  | nil => exact hperm
  | cons k v entries ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (Raw₀.interSmallerFn m₁ acc k)
      (List.interSmallerFn (toListModel m₁.1.buckets) accEntries k)
      (by
        unfold Raw₀.interSmallerFn
        split
        · exact wfImp_insert hacc
        · exact hacc)
      (toListModel_interSmallerFn m₁ acc accEntries hm₁ hacc k hperm)

theorem toListModel_inter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m₁ m₂ : Raw₀ α β) (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    toListModel (m₁.inter m₂).1.buckets ~
      (toListModel m₁.1.buckets).filter
        (fun p => List.containsKey p.1 (toListModel m₂.1.buckets)) := by
  unfold Raw₀.inter
  split
  · simpa only [contains_eq_containsKey h₂] using
      (toListModel_filter m₁ (fun k _ => m₂.contains k))
  · exact (toListModel_interSmaller m₁ m₂.1 h₁).trans
      (List.interSmaller_perm_filter _ _ h₁.distinct)

theorem Raw₀.wfImp_inter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw α β} {h₁ : 0 < m₁.keyArray.size} {h₂ : 0 < m₂.keyArray.size}
    (hm₁ : Raw.WFImp m₁) :
    Raw.WFImp (Raw₀.inter ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1 := by
  unfold Raw₀.inter
  split
  · exact wfImp_filter (m := (⟨m₁, h₁⟩ : Raw₀ α β)) hm₁
  · exact wfImp_interSmaller ⟨m₁, h₁⟩ m₂

theorem eraseManyEntries_eq_eraseListₘ_toListModel [BEq α] [Hashable α]
    (m m₂ : Raw₀ α β) :
    Raw₀.eraseManyEntries m m₂.1 =
      Raw₀.eraseListₘ m ((toListModel m₂.1.buckets).map (·.1)) := by
  simp only [Raw₀.eraseManyEntries, bind_pure]
  simp only [ForIn.forIn]
  simp only [Raw.forIn_eq_forIn_toListModel, forIn_pure_yield_eq_foldl, Id.run_pure]
  generalize toListModel m₂.1.buckets = entries
  suffices ∀ (target : { m' // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' : Raw₀ α β} {a : α}, P m'' → P (m''.erase a)) → P m → P m' }),
      (entries.foldl (fun target p =>
        ⟨target.1.erase p.1, fun P step base => step (target.2 P step base)⟩) target).1 =
        Raw₀.eraseListₘ target.1 (entries.map (·.1)) from this _
  intro target
  induction entries using List.assoc_induction generalizing target with
  | nil => rfl
  | cons k v entries ih =>
    rw [List.foldl_cons, List.map_cons]
    exact ih _

theorem toListModel_diff [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m₁ m₂ : Raw₀ α β} (h₁ : Raw.WFImp m₁.1) (h₂ : Raw.WFImp m₂.1) :
    toListModel (m₁.diff m₂).1.buckets ~
      (toListModel m₁.1.buckets).filter
        (fun p => !List.contains ((toListModel m₂.1.buckets).map Sigma.fst) p.fst) := by
  unfold Raw₀.diff
  split
  · simpa only [contains_eq_containsKey h₂,
      List.containsKey_eq_contains_map_fst] using
      (toListModel_filter m₁ (fun k _ => !m₂.contains k))
  · rw [eraseManyEntries_eq_eraseListₘ_toListModel]
    exact (toListModel_eraseListₘ h₁).trans
      (List.eraseList_perm_filter_not_contains _ _ h₁.distinct)

theorem Raw₀.wf_diff₀ [BEq α] [Hashable α]
    {m₁ m₂ : Raw α β} {h₁ : 0 < m₁.keyArray.size} {h₂ : 0 < m₂.keyArray.size}
    (hm₁ : m₁.WF) : (Raw₀.diff ⟨m₁, h₁⟩ ⟨m₂, h₂⟩).1.WF := by
  unfold Raw₀.diff
  split
  · exact Raw.WF.filter₀ (f := fun k _ => !Raw₀.contains ⟨m₂, h₂⟩ k) hm₁
  · exact (Raw₀.eraseManyEntries ⟨m₁, h₁⟩ m₂).2
      (fun m => m.1.WF) (fun h => .erase₀ h) hm₁

namespace Raw

theorem WF.out [BEq α] [Hashable α] [i₁ : EquivBEq α] [i₂ : LawfulHashable α]
    {m : Raw α β} (h : m.WF) : Raw.WFImp m := by
  induction h generalizing i₁ i₂ with
  | wf _ h => exact h
  | emptyWithCapacity₀ => exact Raw₀.wfImp_emptyWithCapacity
  | insert₀ _ h => exact Raw₀.wfImp_insert h
  | containsThenInsert₀ _ h => exact Raw₀.wfImp_containsThenInsert h
  | containsThenInsertIfNew₀ _ h => exact Raw₀.wfImp_containsThenInsertIfNew h
  | erase₀ _ h => exact Raw₀.wfImp_erase h
  | insertIfNew₀ _ h => exact Raw₀.wfImp_insertIfNew h
  | getThenInsertIfNew?₀ _ h => exact Raw₀.wfImp_getThenInsertIfNew? h
  | filter₀ _ h => exact Raw₀.wfImp_filter h
  | constGetThenInsertIfNew?₀ _ h => exact Raw₀.Const.wfImp_getThenInsertIfNew? h
  | modify₀ _ h => exact Raw₀.wfImp_modify h
  | constModify₀ _ h => exact Raw₀.Const.wfImp_modify h
  | alter₀ _ h => exact Raw₀.wfImp_alter h
  | constAlter₀ _ h => exact Raw₀.Const.wfImp_alter h
  | inter₀ _ _ h _ => exact Raw₀.wfImp_inter h

end Raw

theorem Raw₀.wf_filterMap₀ [BEq α] [Hashable α] {m : Raw₀ α β}
    (h : m.1.WF) {gamma : α → Type w} {f : (a : α) → β a → Option (gamma a)} :
    (m.filterMap f).1.WF :=
  .wf (m.filterMap f).2 (wfImp_filterMap (Raw.WF.out h))

theorem Raw₀.wf_map₀ [BEq α] [Hashable α] {m : Raw₀ α β}
    (h : m.1.WF) {gamma : α → Type w} {f : (a : α) → β a → gamma a} :
    (m.map f).1.WF :=
  .wf (m.map f).2 (wfImp_map (Raw.WF.out h))

theorem insertMany_list_eq_foldl [BEq α] [Hashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} :
    (Raw₀.insertMany m l).1 =
      l.foldl (init := m) (fun acc p => acc.insert p.1 p.2) := by
  simpa [Raw₀.insertMany] using
    (List.foldl_hom Subtype.val (by simp)).symm

theorem insertManyIfNew_list_eq_foldl [BEq α] [Hashable α]
    {m : Raw₀ α β} {l : List ((a : α) × β a)} :
    (Raw₀.insertManyIfNew m l).1 =
      l.foldl (init := m) (fun acc p => acc.insertIfNew p.1 p.2) := by
  simpa [Raw₀.insertManyIfNew] using
    (List.foldl_hom Subtype.val (by simp)).symm

theorem Raw₀.Const.insertMany_list_eq_foldl {beta : Type v} [BEq α] [Hashable α]
    {m : Raw₀ α (fun _ => beta)} {l : List (α × beta)} :
    (Raw₀.Const.insertMany m l).1 =
      l.foldl (init := m) (fun acc p => acc.insert p.1 p.2) := by
  simpa [Raw₀.Const.insertMany] using
    (List.foldl_hom Subtype.val (by simp)).symm

theorem Raw₀.Const.insertManyIfNewUnit_list_eq_foldl [BEq α] [Hashable α]
    {m : Raw₀ α (fun _ => Unit)} {l : List α} :
    (Raw₀.Const.insertManyIfNewUnit m l).1 =
      l.foldl (init := m) (fun acc a => acc.insertIfNew a ()) := by
  simpa [Raw₀.Const.insertManyIfNewUnit] using
    (List.foldl_hom Subtype.val (by simp)).symm

theorem filterMap_eq_filter {m : Raw₀ α β} {f : (a : α) → β a → Bool} :
    m.filterMap (fun k => Option.guard (fun v => f k v)) = m.filter f := by
  unfold Raw₀.filter
  congr

theorem filterMap_eq_map [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {gamma : α → Type w} (m : Raw₀ α β) (f : (a : α) → β a → gamma a)
    (_h : m.1.WF) : m.filterMap (fun k v => some (f k v)) = m.map f := rfl

namespace Raw₀

/- These names are the proof-facing interface consumed by `RawLemmas`. The underlying
   implementation lemmas remain shared with the low-level array proofs above. -/
abbrev toListModel_insert := @Std.DHashMap.Internal.toListModel_insert
abbrev toListModel_erase := @Std.DHashMap.Internal.toListModel_erase
abbrev toListModel_insertIfNew := @Std.DHashMap.Internal.toListModel_insertIfNew
abbrev toListModel_insertMany_list := @Std.DHashMap.Internal.toListModel_insertMany_list
abbrev toListModel_union := @Std.DHashMap.Internal.toListModel_union
abbrev toListModel_inter := @Std.DHashMap.Internal.toListModel_inter
abbrev toListModel_diff := @Std.DHashMap.Internal.toListModel_diff
abbrev toListModel_alter := @Std.DHashMap.Internal.toListModel_alter
abbrev toListModel_modify := @Std.DHashMap.Internal.toListModel_modify
abbrev toListModel_filter := @Std.DHashMap.Internal.toListModel_filter
abbrev toListModel_map := @Std.DHashMap.Internal.toListModel_map
abbrev toListModel_filterMap := @Std.DHashMap.Internal.toListModel_filterMap

abbrev contains_eq_containsKey := @Std.DHashMap.Internal.contains_eq_containsKey
abbrev get?_eq_getValueCast? := @Std.DHashMap.Internal.get?_eq_getValueCast?
abbrev get_eq_getValueCast := @Std.DHashMap.Internal.get_eq_getValueCast
abbrev get!_eq_getValueCast! := @Std.DHashMap.Internal.get!_eq_getValueCast!
abbrev getD_eq_getValueCastD := @Std.DHashMap.Internal.getD_eq_getValueCastD
abbrev getKey?_eq_getKey? := @Std.DHashMap.Internal.getKey?_eq_getKey?
abbrev getKey_eq_getKey := @Std.DHashMap.Internal.getKey_eq_getKey
abbrev getKeyD_eq_getKeyD := @Std.DHashMap.Internal.getKeyD_eq_getKeyD
abbrev getKey!_eq_getKey! := @Std.DHashMap.Internal.getKey!_eq_getKey!
abbrev getEntry_eq_getEntry := @Std.DHashMap.Internal.getEntry_eq_getEntry
abbrev getEntry?_eq_getEntry? := @Std.DHashMap.Internal.getEntry?_eq_getEntry?
abbrev getEntryD_eq_getEntryD := @Std.DHashMap.Internal.getEntryD_eq_getEntryD
abbrev getEntry!_eq_getEntry! := @Std.DHashMap.Internal.getEntry!_eq_getEntry!
abbrev beq_eq_beqModel := @Std.DHashMap.Internal.beq_eq_beqModel

end Raw₀

end Std.DHashMap.Internal
