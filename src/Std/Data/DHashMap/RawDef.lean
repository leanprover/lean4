/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
module

prelude
public import Std.Data.DHashMap.Internal.AssocList.Basic
public import Init.Data.Array.Basic
public import Init.Data.Erased
public import Init.Data.Fin.Fold
import Init.Data.Array.Lemmas
import Init.ByCases
import Init.Classical
import Init.Omega
import Init.WFTactics

public section

/-!
# Definition of `DHashMap.Raw`

This file defines the type `Std.Data.DHashMap.Raw`. All of its functions are defined in the module
`Std.Data.DHashMap.Basic`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.DHashMap

open Internal

namespace Raw

/-- The type-level alignment condition for one pair of key and value cells. -/
@[expose] def CellsMatch {α : Type u} {β : α → Type v} (key : NOption α)
    (value : NOption (NSigma β)) : Prop :=
  match key, value with
  | .none, .none => True
  | .some _, .none => True
  | .some k, .some v => v.fst = k
  | _, _ => False

/-- The type-level alignment condition for the parallel key and value arrays. -/
@[expose] def KeysValues {α : Type u} {β : α → Type v} (keys : Array (NOption α))
    (values : Array (NOption (NSigma β))) : Prop :=
  keys.size = values.size ∧
    ∀ (i : Nat) (hk : i < keys.size) (hv : i < values.size), CellsMatch keys[i] values[i]

end Raw

/--
Dependent hash maps whose hashing and probing invariant is not bundled with the table. That
invariant is called `Raw.WF`. The representation does bundle the erased alignment proof needed for
its separate dependent key and value arrays, so `Raw` cannot currently be used in nested inductive
types. When in doubt, prefer `DHashMap` over `DHashMap.Raw`. Lemmas about the operations on
`Std.Data.DHashMap.Raw` are available in the module `Std.Data.DHashMap.RawLemmas`.

The hash table is backed by two `Array`s. Users should make sure that the hash map is used linearly to
avoid expensive copies.

This is a linear-probing hash table. Keys and values are stored in separate flat arrays. Empty cells
are represented by `NOption.none`; values use `NSigma` so that their keys are available to the logic
but erased at runtime. The number of cells is always a power of two. The hash map doubles its size
before inserting an element that would make it more than 75% full.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.
-/
structure Raw (α : Type u) (β : α → Type v) where
  /-- The number of mappings present in the hash map -/
  size : Nat
  /-- The keys stored in the hash table. `NOption.none` represents a never-used cell. -/
  keyArray : Array (NOption α)
  /-- The values stored in the hash table. `NOption.none` represents an unoccupied cell. -/
  valueArray : Array (NOption (NSigma β))
  /-- The erased proof that corresponding key and value cells have compatible types. -/
  keysValues : Raw.KeysValues keyArray valueArray

namespace Raw

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w'}

/-- The key and value arrays have the same number of cells. -/
theorem keyArray_size_eq_valueArray_size (m : Raw α β) :
    m.keyArray.size = m.valueArray.size :=
  m.keysValues.1

/-- Internal implementation detail of the hash map. -/
theorem keysValues_replicate (n : Nat) :
    KeysValues (Array.replicate n (NOption.none : NOption α))
      (Array.replicate n (NOption.none : NOption (NSigma β))) := by
  simp only [KeysValues]
  constructor
  · simp
  · intro i hk hv
    simp [CellsMatch]

/-- Internal implementation detail of the hash map. -/
theorem keysValues_replicateValuesNone (keys : Array (NOption α)) :
    KeysValues keys (Array.replicate keys.size (NOption.none : NOption (NSigma β))) := by
  simp only [KeysValues]
  constructor
  · simp
  · intro i hk hv
    have hv' : i < (Array.replicate keys.size (NOption.none : NOption (NSigma β))).size := hv
    rw [Array.getElem_replicate hv']
    cases hkey : keys[i] <;> simp [CellsMatch]

/-- Internal implementation detail of the hash map. -/
theorem keysValues_set {keys : Array (NOption α)} {values : Array (NOption (NSigma β))}
    (h : KeysValues keys values) (i : Nat) (hi : i < keys.size)
    (hiv : i < values.size) (key : NOption α) (value : NOption (NSigma β))
    (hcell : CellsMatch key value) :
    KeysValues (keys.set i key) (values.set i value) := by
  simp only [KeysValues] at h ⊢
  constructor
  · simp [h.1]
  · intro j hjk hjv
    by_cases hji : j = i
    · subst j
      simpa using hcell
    · have hjk' : j < keys.size := by simpa using hjk
      have hjv' : j < values.size := by simpa using hjv
      rw [Array.getElem_set_ne hi hjk' (Ne.symm hji)]
      rw [Array.getElem_set_ne hiv hjv' (Ne.symm hji)]
      exact h.2 j hjk' hjv'

/-- Replaces one pair of cells and the cached number of mappings. -/
@[noinline, expose] def setCell (m : Raw α β) (size : Nat) (i : Nat) (hi : i < m.keyArray.size)
    (key : NOption α) (value : NOption (NSigma β)) (hcell : CellsMatch key value) : Raw α β :=
  have hiv : i < m.valueArray.size := by simpa [m.keysValues.1] using hi
  { size
    keyArray := m.keyArray.set i key
    valueArray := m.valueArray.set i value
    keysValues := by
      exact keysValues_set m.keysValues i hi hiv key value hcell }

/-- Internal implementation detail of the hash map. -/
theorem keysValues_setCell (m : Raw α β) (size i : Nat) (hi : i < m.keyArray.size)
    (_h : KeysValues m.keyArray m.valueArray) (key : NOption α)
    (value : NOption (NSigma β)) (hcell : CellsMatch key value) :
    KeysValues (m.setCell size i hi key value hcell).keyArray
      (m.setCell size i hi key value hcell).valueArray := by
  exact (m.setCell size i hi key value hcell).keysValues

/-- Stores a mapping in one cell. -/
@[noinline, expose] def setEntry (m : Raw α β) (size : Nat) (i : Nat) (hi : i < m.keyArray.size)
    (a : α) (b : β a) : Raw α β :=
  m.setCell size i hi (.some a) (.some (.mk a b)) (by simp [CellsMatch])

/-- Internal implementation detail of the hash map. -/
theorem keysValues_setEntry (m : Raw α β) (size i : Nat) (hi : i < m.keyArray.size)
    (h : KeysValues m.keyArray m.valueArray) (a : α) (b : β a) :
    KeysValues (m.setEntry size i hi a b).keyArray (m.setEntry size i hi a b).valueArray := by
  apply keysValues_setCell
  exact h

/-- Empties one cell. -/
@[noinline, expose] def clearCell (m : Raw α β) (size : Nat) (i : Nat) (_hi : i < m.keyArray.size) :
    Raw α β :=
  have hiv : i < m.valueArray.size := by simpa [m.keysValues.1] using _hi
  { size
    keyArray := m.keyArray
    valueArray := m.valueArray.set i .none
    keysValues := by
      have hcell : CellsMatch m.keyArray[i] (NOption.none : NOption (NSigma β)) := by
        cases hkey : m.keyArray[i] <;> simp [CellsMatch]
      simpa only [Array.set_getElem_self _hi] using
        keysValues_set m.keysValues i _hi hiv m.keyArray[i] .none hcell }

/-- Internal implementation detail of the hash map. -/
theorem keysValues_clearCell (m : Raw α β) (size i : Nat) (hi : i < m.keyArray.size)
    (_h : KeysValues m.keyArray m.valueArray) :
    KeysValues (m.clearCell size i hi).keyArray (m.clearCell size i hi).valueArray := by
  exact (m.clearCell size i hi).keysValues

/-- Updates a value while retaining the key array. -/
@[noinline, expose] def setValue (m : Raw α β) (size : Nat) (i : Nat)
    (hi : i < m.keyArray.size) (a : α) (hkey : m.keyArray[i] = .some a) (b : β a) : Raw α β :=
  have hiv : i < m.valueArray.size := by simpa [m.keysValues.1] using hi
  { size
    keyArray := m.keyArray
    valueArray := m.valueArray.set i (.some (.mk a b))
    keysValues := by
      have hcell : CellsMatch m.keyArray[i] (.some (.mk a b)) := by
        simp [hkey, CellsMatch]
      simpa only [Array.set_getElem_self hi] using
        keysValues_set m.keysValues i hi hiv m.keyArray[i] (.some (.mk a b)) hcell }

/-- Writing the key already present in a cell is the same as updating only its value. -/
theorem setEntry_eq_setValue (m : Raw α β) (size i : Nat) (hi : i < m.keyArray.size)
    (a : α) (hkey : m.keyArray[i] = .some a) (b : β a) :
    m.setEntry size i hi a b = m.setValue size i hi a hkey b := by
  have hkeys : m.keyArray.set i (.some a) = m.keyArray := by
    apply Array.ext (by simp)
    intro j hjSet hj
    by_cases hji : j = i
    · subst j
      simpa using hkey.symm
    · rw [Array.getElem_set_ne hi hj (Ne.symm hji)]
  simp [setEntry, setCell, setValue, hkeys]

/-- Reconstructs an entry from a pair of matching key and value cells. -/
@[inline, expose] def CellsMatch.entry? :
    (key : NOption α) → (value : NOption (NSigma β)) → CellsMatch key value →
      Option ((a : α) × β a)
  | .none, _, _ => .none
  | .some _, .none, _ => .none
  | .some k, .some v, h => .some ⟨k, h ▸ v.snd⟩

/-- Reconstructs the proof-facing entry represented by a value cell. -/
@[inline, expose] noncomputable def cellEntry? (_key : NOption α) (value : NOption (NSigma β)) :
    Option ((a : α) × β a) :=
  match _key, value with
  | .some _, .some v => .some ⟨v.fst, v.snd⟩
  | _, _ => .none

theorem cellEntry_eq_entry (key : NOption α) (value : NOption (NSigma β))
    (h : CellsMatch key value) : cellEntry? key value = h.entry? := by
  cases key <;> cases value
  · rfl
  · simp [CellsMatch] at h
  · rfl
  · simp only [cellEntry?, CellsMatch.entry?]
    cases h
    rfl

/-- Executable reconstruction of an entry using the erased cell-alignment proof. -/
@[inline] def entryAtInBoundsImpl? (b : Raw α β) (i : Nat) (h : i < b.keyArray.size) :
    Option ((a : α) × β a) :=
  have hv : i < b.valueArray.size := by simpa [b.keysValues.1] using h
  CellsMatch.entry? b.keyArray[i] b.valueArray[i] (b.keysValues.2 i h hv)

/-- Returns the entry in an in-bounds cell, if its key and value cells are both occupied. -/
@[inline, expose]
noncomputable def entryAtInBounds? (b : Raw α β) (i : Nat) (h : i < b.keyArray.size) :
    Option ((a : α) × β a) :=
  if hv : i < b.valueArray.size then cellEntry? b.keyArray[i] b.valueArray[i] else none

@[csimp] theorem entryAtInBounds_eq_entryAtInBoundsImpl :
    @entryAtInBounds? = @entryAtInBoundsImpl? := by
  funext α β b i h
  simp only [entryAtInBounds?, entryAtInBoundsImpl?]
  have hv : i < b.valueArray.size := by simpa [b.keysValues.1] using h
  simp only [hv, ↓reduceDIte]
  have hcell := b.keysValues.2 i h hv
  exact cellEntry_eq_entry b.keyArray[i] b.valueArray[i] hcell

/-- A reconstructed entry's key is the key stored in the corresponding key cell. -/
theorem keyArray_eq_some_of_entryAtInBounds_eq_some (b : Raw α β) (i : Nat)
    (hi : i < b.keyArray.size) (k : α) (v : β k)
    (hentry : b.entryAtInBounds? i hi = some ⟨k, v⟩) :
    b.keyArray[i] = .some k := by
  have hiv : i < b.valueArray.size := by simpa [b.keysValues.1] using hi
  have hcell := b.keysValues.2 i hi hiv
  unfold entryAtInBounds? at hentry
  rw [dite_eq_left hiv] at hentry
  cases hkey : b.keyArray[i] with
  | none => simp [cellEntry?, hkey] at hentry
  | some key =>
    cases hvalue : b.valueArray[i] with
    | none => simp [cellEntry?, hkey, hvalue] at hentry
    | some value =>
      rw [hkey, hvalue] at hentry
      change (some (Sigma.mk value.fst value.snd) : Option ((a : α) × β a)) =
        some (Sigma.mk k v) at hentry
      have hpair : Sigma.mk value.fst value.snd = Sigma.mk k v := Option.some.inj hentry
      have hfst : value.fst = k := congrArg Sigma.fst hpair
      have hmatch : value.fst = key := by
        simpa [CellsMatch, hkey, hvalue] using hcell
      simp [hmatch.symm.trans hfst]

/-- Returns the entry in a cell, or `none` when the index is out of bounds or the cell is empty. -/
@[inline, expose] def entryAt? (b : Raw α β) (i : Nat) : Option ((a : α) × β a) :=
  if h : i < b.keyArray.size then b.entryAtInBounds? i h else none

/-- Collects the occupied cells at or after `i` into the proof-facing associative list. -/
@[expose] def entriesFrom (b : Raw α β) (i : Nat) : DHashMap.Internal.AssocList α β :=
  if h : i < b.keyArray.size then
    match b.entryAtInBounds? i h with
    | .none => b.entriesFrom (i + 1)
    | .some ⟨k, v⟩ => .cons k v (b.entriesFrom (i + 1))
  else
    .nil
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ h

/--
A proof-facing separate-bucket view of the flat table.

The sole bucket lists entries in physical-cell order. This definition is used only by the
verification model; executable operations access `keyArray` and `valueArray` directly.
-/
@[expose] def buckets (b : Raw α β) : Array (DHashMap.Internal.AssocList α β) :=
  #[b.entriesFrom 0]

/-- Folds over occupied cells at or after `i`. -/
@[specialize, expose] def foldMFrom [Monad m] (f : δ → (a : α) → β a → m δ) (b : Raw α β)
    (acc : δ) (i : Nat) : m δ := do
  if h : i < b.keyArray.size then
    match b.entryAtInBounds? i h with
    | .none => foldMFrom f b acc (i + 1)
    | .some ⟨k, v⟩ => foldMFrom f b (← f acc k v) (i + 1)
  else
    pure acc
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ h

/--
Monadically computes a value by folding the given function over the mappings in the hash
map in some order.
-/
@[specialize] def foldM [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ)
    (b : Raw α β) : m δ :=
  foldMFrom f b init 0

/-- Folds occupied cells at or after `i` in reverse physical order. -/
@[specialize, expose] def foldRevMFrom [Monad m] (f : δ → (a : α) → β a → m δ)
    (b : Raw α β) (acc : δ) (i : Nat) : m δ := do
  if h : i < b.keyArray.size then
    match b.entryAtInBounds? i h with
    | .none => foldRevMFrom f b acc (i + 1)
    | .some ⟨k, v⟩ => f (← foldRevMFrom f b acc (i + 1)) k v
  else
    pure acc
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ h

/-- Folds the given function over the mappings in the hash map in some order. -/
@[inline] def fold (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldM (pure <| f · · ·) init)

/-- Carries out a monadic action on each mapping in the hash map in some order. -/
@[inline] def forM [Monad m] (f : (a : α) → β a → m PUnit) (b : Raw α β) : m PUnit :=
  b.foldM (fun _ a v => f a v) ⟨⟩

/-- Runs a `for`-loop body over occupied cells at or after `i`. -/
@[specialize, expose] def forInFrom [Monad m] (f : (a : α) → β a → δ → m (ForInStep δ))
    (b : Raw α β) (acc : δ) (i : Nat) : m δ := do
  if h : i < b.keyArray.size then
    match b.entryAtInBounds? i h with
    | .none => forInFrom f b acc (i + 1)
    | .some ⟨k, v⟩ =>
      match ← f k v acc with
      | .done acc => pure acc
      | .yield acc => forInFrom f b acc (i + 1)
  else
    pure acc
termination_by b.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ h

/-- Support for the `for` loop construct in `do` blocks. -/
@[specialize] def forIn [Monad m] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ)
    (b : Raw α β) : m δ :=
  forInFrom f b init 0

instance [Monad m] : ForM m (Raw α β) ((a : α) × β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance [Monad m] : ForIn m (Raw α β) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

/-- Checks if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline] def all (m : Raw α β) (p : (a : α) → β a → Bool) : Bool := Id.run do
  for a in m do
    if ¬ p a.1 a.2 then return false
  return true

/-- Checks if any element satisfies the predicate, short-circuiting if a predicate succeeds. -/
@[inline] def any (m : Raw α β) (p : (a : α) → β a → Bool) : Bool := Id.run do
  for a in m do
    if p a.1 a.2 then return true
  return false

end Raw

end Std.DHashMap
