/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.ByCases
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Data.List.Pairwise
public import Init.Grind
public import Init.Data.Int.OfNat
public import Std.Data.HashMap

public section

/-!
# IndexMultiMap

This module defines a generic `IndexMultiMap` type that maps keys to multiple values.
The implementation stores entries in a flat array for iteration and an index HashMap
for fast key lookups. Each key always has at least one associated value.
-/

namespace Std.Internal

open Std

set_option linter.all true

/--
A structure for managing ordered key-value pairs where each key can have multiple values.
-/
structure IndexMultiMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where

  /--
  Flat array of all key-value entries in insertion order.
  -/
  entries : Array (α × β)

  /--
  Maps each key to its indices in `entries`. Each array is non-empty.
  -/
  indexes : HashMap α (Array Nat)

  /--
  Invariant: every key in `indexes` maps to a non-empty array of valid indices into `entries`
  whose keys compare equal to it. Each index array contains no duplicates.
  -/
  validity : ∀ k : α, (p : k ∈ indexes) →
            let idx := (indexes.get k p);
            idx.size > 0 ∧ (∀ i ∈ idx, ∃ h : i < entries.size, (entries[i]'h).fst == k) ∧
            idx.toList.Nodup

  /--
  Invariant: every position in `entries` occurs in an index array.
  -/
  coverage : ∀ i, i < entries.size → ∃ key, ∃ h : key ∈ indexes, i ∈ indexes.get key h

deriving Repr

instance [BEq α] [Hashable α] [Inhabited α] [Inhabited β] : Inhabited (IndexMultiMap α β) where
  default := ⟨#[], .emptyWithCapacity, by intro h p; simp at p, by simp⟩

namespace IndexMultiMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

instance : Membership α (IndexMultiMap α β) where
  mem map key := key ∈ map.indexes

instance (key : α) (map : IndexMultiMap α β) : Decidable (key ∈ map) :=
  inferInstanceAs (Decidable (key ∈ map.indexes))

/--
Retrieves all values for the given key.
-/
@[inline]
def getAll (map : IndexMultiMap α β) (key : α) (h : key ∈ map) : Array β :=
  let entries := map.indexes.get key h |>.mapFinIdx fun idx _ h₁ =>
    let proof := map.validity key h |>.right.left _ (Array.getElem_mem h₁)
    map.entries[(map.indexes.get key h)[idx]]'proof.1 |>.snd

  entries

/--
Retrieves the first value for the given key.
-/
@[inline]
def get (map : IndexMultiMap α β) (key : α) (h : key ∈ map) : β :=
  let ⟨nonEmpty, isIn, _⟩ := map.validity key h
  let entry := ((map.indexes.get key h)[0]'nonEmpty)

  let proof := map.validity key h |>.right.left
    entry
    (by simp only [entry, HashMap.get_eq_getElem, Array.getElem_mem])

  map.entries[entry]'proof.1 |>.snd

/--
Retrieves all values for the given key, or `none` if the key is absent.
-/
@[inline]
def getAll? (map : IndexMultiMap α β) (key : α) : Option (Array β) :=
  if h : key ∈ map then
    some (map.getAll key h)
  else
    none

/--
Retrieves the first value for the given key, or `none` if the key is absent.
-/
@[inline]
def get? (map : IndexMultiMap α β) (key : α) : Option β :=
  if h : key ∈ map then
    some (map.get key h)
  else
    none

/--
Checks if the key-value pair is present in the map.
-/
@[inline]
def hasEntry (map : IndexMultiMap α β) [BEq β] (key : α) (value : β) : Bool :=
  map.getAll? key
  |>.bind (fun arr => arr.find? (· == value))
  |>.isSome

/--
Retrieves the last value for the given key.
Returns `none` if the key is absent.
-/
@[inline]
def getLast? (map : IndexMultiMap α β) (key : α) : Option β :=
  match map.getAll? key with
  | none => none
  | some idxs => idxs.back?

/--
Like `get?`, but returns a default value if absent.
-/
@[inline]
def getD (map : IndexMultiMap α β) (key : α) (d : β) : β :=
  map.get? key |>.getD d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! [Inhabited β] (map : IndexMultiMap α β) (key : α) : β :=
  map.get? key |>.get!

/--
Inserts a new key-value pair into the map.
If the key already exists, appends the value to existing values.
-/
@[inline]
def insert [EquivBEq α] [LawfulHashable α] (map : IndexMultiMap α β) (key : α) (value : β) : IndexMultiMap α β :=
  let i := map.entries.size
  let entries := map.entries.push (key, value)

  let f := fun
    | some idxs => some (idxs.push i)
    | none => some #[i]

  let indexes := map.indexes.alter key f

  { entries, indexes, validity := ?_, coverage := by
      intro j hj
      by_cases h : j < map.entries.size
      · obtain ⟨k, hk, hjk⟩ := map.coverage j h
        refine ⟨k, ?_, ?_⟩ <;> grind [HashMap.getElem_congr, HashMap.mem_congr]
      · refine ⟨key, ?_, ?_⟩ <;> grind }
where finally
  have _ := map.validity
  grind [BEq.trans]

/--
Inserts multiple values for a given key, appending to any existing values.
-/
@[inline]
def insertMany [EquivBEq α] [LawfulHashable α] (map : IndexMultiMap α β) (key : α) (values : Array β) : IndexMultiMap α β :=
  values.foldl (insert · key) map

/--
Creates an empty multimap.
-/
def empty : IndexMultiMap α β :=
  ⟨#[], .emptyWithCapacity, by intro h p; simp at p, by simp⟩

/--
Creates a multimap from a list of key-value pairs.
-/
def ofList [EquivBEq α] [LawfulHashable α] (pairs : List (α × β)) : IndexMultiMap α β :=
  pairs.foldl (fun acc (k, v) => acc.insert k v) empty

/--
Checks if a key exists in the map.
-/
@[inline]
def contains (map : IndexMultiMap α β) (key : α) : Bool :=
  map.indexes.contains key

/--
Updates all values associated with `key` by applying `f` to each one.
If the key is absent, returns the map unchanged.
-/
@[inline]
def update [EquivBEq α] [LawfulHashable α] (map : IndexMultiMap α β) (key : α) (f : β → β) : IndexMultiMap α β :=
  if key ∉ map then
    map
  else
    { map with
      entries := map.entries.map (fun (k, v) => (k, if k == key then f v else v))
      validity := ?_
      coverage := by simpa using map.coverage }
where finally
  have _ := map.validity
  grind

/--
Replaces the last value associated with `key` with `value`.
If the key is absent, returns the map unchanged.
-/
@[inline]
def replaceLast [EquivBEq α] (map : IndexMultiMap α β) (key : α) (value : β) : IndexMultiMap α β :=
  if h : key ∈ map then
    let idxs := map.indexes.get key h
    let ⟨nonEmpty, isIn, _⟩ := map.validity key h
    let lastPos : Fin idxs.size := ⟨idxs.size - 1, Nat.sub_lt nonEmpty (by omega)⟩
    let lastIdx : Nat := idxs[lastPos]
    have lastIdxValid : lastIdx < map.entries.size := (isIn lastIdx (Array.getElem_mem lastPos.isLt)).1
    let entries := map.entries.set (Fin.mk lastIdx lastIdxValid) (key, value)
    { map with entries, validity := ?_, coverage := by simpa [entries] using map.coverage }
  else
    map
where finally
  have _ := map.validity
  grind [BEq.symm, BEq.trans]

/--
Removes a key and all its values from the map. This function rebuilds the entire
`entries` array and `indexes` map from scratch by filtering out all pairs whose
key matches, then re-inserting the survivors.
-/
@[inline]
def erase [EquivBEq α] [LawfulHashable α] (map : IndexMultiMap α β) (key : α) : IndexMultiMap α β :=
  if key ∉ map then
    map
  else
    map.entries.foldl (fun acc (k,v) => if ¬(key == k) then acc.insert k v else acc) empty

/--
Removes multiple keys and all their associated values from the map.
Keys not present in the map are ignored.
-/
@[inline]
def eraseMany [EquivBEq α] [LawfulHashable α] (map : IndexMultiMap α β) (keys : Array α) : IndexMultiMap α β :=
  map.entries.foldl (fun acc (k,v) => if ¬(keys.contains k) then acc.insert k v else acc) empty

/--
Gets the number of entries in the map.
-/
@[inline]
def size (map : IndexMultiMap α β) : Nat :=
  map.entries.size

/--
Checks if the map is empty.
-/
@[inline]
def isEmpty (map : IndexMultiMap α β) : Bool :=
  map.entries.isEmpty

/--
Converts the multimap to an array of key-value pairs (flattened).
-/
def toArray (map : IndexMultiMap α β) : Array (α × β) :=
  map.entries

/--
Converts the multimap to a list of key-value pairs (flattened).
-/
def toList (map : IndexMultiMap α β) : List (α × β) :=
  map.entries.toList

/--
Merges two multimaps, combining values for shared keys.
-/
def merge [EquivBEq α] [LawfulHashable α] (m1 m2 : IndexMultiMap α β) : IndexMultiMap α β :=
  m2.entries.foldl (fun acc (k, v) => acc.insert k v) m1

instance : EmptyCollection (IndexMultiMap α β) :=
  ⟨IndexMultiMap.empty⟩

instance [EquivBEq α] [LawfulHashable α] : Singleton (α × β) (IndexMultiMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : IndexMultiMap α β).insert a b⟩

instance [EquivBEq α] [LawfulHashable α] : Insert (α × β) (IndexMultiMap α β) :=
  ⟨fun ⟨a, b⟩ m => m.insert a b⟩

instance [EquivBEq α] [LawfulHashable α] : Union (IndexMultiMap α β) :=
  ⟨merge⟩

instance [Monad m] : ForIn m (IndexMultiMap α β) (α × β) where
  forIn map b f := forIn map.entries b f

end Std.Internal.IndexMultiMap
