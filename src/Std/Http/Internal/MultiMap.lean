/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Array.Lemmas
public import Init.Data.Option.BasicAux
import Init.Omega

public section

/-!
# MultiMap

This module defines a generic `MultiMap` type that maps keys to multiple values while
remembering the order in which entries were inserted.

Entries live in one array and lookups scan it. Header maps hold at most a few dozen entries and see a
handful of lookups per message, so a scan costs less than maintaining any index on insert.
-/

namespace Std.Internal

set_option linter.all true

/--
A structure for managing ordered key-value pairs where each key can have multiple values.
-/
structure MultiMap (α : Type u) (β : Type v) where

  /--
  All key-value entries in insertion order.
  -/
  entries : Array (α × β)

deriving Inhabited, Repr

namespace MultiMap

variable {α : Type u} {β : Type v}

instance [BEq α] : Membership α (MultiMap α β) where
  mem map key := map.entries.any (·.1 == key)

instance [BEq α] (key : α) (map : MultiMap α β) : Decidable (key ∈ map) :=
  inferInstanceAs (Decidable (map.entries.any (·.1 == key) = true))

/--
Position of the first entry at or after `i` whose key is `key`, or `map.entries.size` if there is
none.
-/
@[specialize]
def findIdxFrom [BEq α] (map : MultiMap α β) (key : α) (i : Nat) : Nat :=
  if h : i < map.entries.size then
    if map.entries[i].1 == key then i else map.findIdxFrom key (i + 1)
  else
    map.entries.size
termination_by map.entries.size - i

/--
Position of the last entry below `i` whose key is `key`, or `map.entries.size` if there is none.
-/
@[specialize]
def findLastIdxBelow [BEq α] (map : MultiMap α β) (key : α) : Nat → Nat
  | 0 => map.entries.size
  | i + 1 =>
    if h : i < map.entries.size then
      if map.entries[i].1 == key then i else map.findLastIdxBelow key i
    else
      map.entries.size

/--
`findIdxFrom` stays in bounds when some entry at or after `i` has the key.
-/
theorem findIdxFrom_lt_size [BEq α] (map : MultiMap α β) (key : α) (i : Nat)
    (h : ∃ j, ∃ _ : j < map.entries.size, i ≤ j ∧ (map.entries[j].1 == key) = true) :
    map.findIdxFrom key i < map.entries.size := by
  fun_induction findIdxFrom map key i with
  | case1 i hi => exact hi
  | case2 i hi hne ih =>
    obtain ⟨j, hj, hij, hjk⟩ := h
    refine ih ⟨j, hj, ?_, hjk⟩
    refine Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hij ?_)
    intro hEq
    subst hEq
    exact hne hjk
  | case3 i hi =>
    obtain ⟨j, hj, hij, _⟩ := h
    omega

/--
The first entry with a key that is in the map lies within `entries`.
-/
theorem findIdxFrom_zero_lt_size [BEq α] {map : MultiMap α β} {key : α} (h : key ∈ map) :
    map.findIdxFrom key 0 < map.entries.size := by
  obtain ⟨j, hj, hjk⟩ := Array.any_eq_true.mp h
  exact map.findIdxFrom_lt_size key 0 ⟨j, hj, Nat.zero_le j, hjk⟩

/--
Retrieves all values for the given key.
-/
@[inline]
def getAll [BEq α] (map : MultiMap α β) (key : α) (_h : key ∈ map) : Array β :=
  map.entries.foldl (init := #[]) fun acc e => if e.1 == key then acc.push e.2 else acc

/--
Retrieves the first value for the given key.
-/
@[inline]
def get [BEq α] (map : MultiMap α β) (key : α) (h : key ∈ map) : β :=
  (map.entries[map.findIdxFrom key 0]'(findIdxFrom_zero_lt_size h)).2

/--
Retrieves all values for the given key, or `none` if the key is absent.
-/
@[inline]
def getAll? [BEq α] (map : MultiMap α β) (key : α) : Option (Array β) :=
  let values := map.entries.foldl (init := #[]) fun acc e => if e.1 == key then acc.push e.2 else acc
  if values.isEmpty then none else some values

/--
Retrieves the first value for the given key, or `none` if the key is absent.
-/
@[inline]
def get? [BEq α] (map : MultiMap α β) (key : α) : Option β :=
  let i := map.findIdxFrom key 0
  if h : i < map.entries.size then some map.entries[i].2 else none

/--
Checks if the key-value pair is present in the map.
-/
@[inline]
def hasEntry [BEq α] [BEq β] (map : MultiMap α β) (key : α) (value : β) : Bool :=
  map.entries.any fun e => e.1 == key && e.2 == value

/--
Retrieves the last value for the given key.
Returns `none` if the key is absent.
-/
@[inline]
def getLast? [BEq α] (map : MultiMap α β) (key : α) : Option β :=
  let i := map.findLastIdxBelow key map.entries.size
  if h : i < map.entries.size then some map.entries[i].2 else none

/--
Like `get?`, but returns a default value if absent.
-/
@[inline]
def getD [BEq α] (map : MultiMap α β) (key : α) (d : β) : β :=
  map.get? key |>.getD d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! [BEq α] [Inhabited β] (map : MultiMap α β) (key : α) : β :=
  map.get? key |>.get!

/--
Inserts a new key-value pair into the map.
If the key already exists, appends the value to existing values.
-/
@[inline]
def insert (map : MultiMap α β) (key : α) (value : β) : MultiMap α β :=
  ⟨map.entries.push (key, value)⟩

/--
Inserts multiple values for a given key, appending to any existing values.
-/
@[inline]
def insertMany (map : MultiMap α β) (key : α) (values : Array β) : MultiMap α β :=
  ⟨values.foldl (fun acc v => acc.push (key, v)) map.entries⟩

/--
Creates an empty multimap.
-/
def empty : MultiMap α β :=
  -- Shared, so the first insert copies it; capacity 8 holds a typical message head without regrowing.
  ⟨.emptyWithCapacity 8⟩

/--
Creates a multimap from a list of key-value pairs.
-/
def ofList (pairs : List (α × β)) : MultiMap α β :=
  ⟨pairs.toArray⟩

/--
Checks if a key exists in the map.
-/
@[inline]
def contains [BEq α] (map : MultiMap α β) (key : α) : Bool :=
  map.entries.any (·.1 == key)

/--
Updates all values associated with `key` by applying `f` to each one.
If the key is absent, returns the map unchanged.
-/
@[inline]
def update [BEq α] (map : MultiMap α β) (key : α) (f : β → β) : MultiMap α β :=
  if map.contains key then
    ⟨map.entries.map fun e => if e.1 == key then (e.1, f e.2) else e⟩
  else
    map

/--
Replaces the last value associated with `key` with `value`.
If the key is absent, returns the map unchanged.
-/
@[inline]
def replaceLast [BEq α] (map : MultiMap α β) (key : α) (value : β) : MultiMap α β :=
  let i := map.findLastIdxBelow key map.entries.size
  if h : i < map.entries.size then ⟨map.entries.set i (key, value)⟩ else map

/--
Removes a key and all its values from the map.
-/
@[inline]
def erase [BEq α] (map : MultiMap α β) (key : α) : MultiMap α β :=
  if map.contains key then ⟨map.entries.filter fun e => !(e.1 == key)⟩ else map

/--
Removes multiple keys and all their associated values from the map.
Keys not present in the map are ignored.
-/
@[inline]
def eraseMany [BEq α] (map : MultiMap α β) (keys : Array α) : MultiMap α β :=
  if map.entries.any (keys.contains ·.1) then
    ⟨map.entries.filter fun e => !keys.contains e.1⟩
  else
    map

/--
Gets the number of entries in the map.
-/
@[inline]
def size (map : MultiMap α β) : Nat :=
  map.entries.size

/--
Checks if the map is empty.
-/
@[inline]
def isEmpty (map : MultiMap α β) : Bool :=
  map.entries.isEmpty

/--
Converts the multimap to an array of key-value pairs (flattened).
-/
def toArray (map : MultiMap α β) : Array (α × β) :=
  map.entries

/--
Converts the multimap to a list of key-value pairs (flattened).
-/
def toList (map : MultiMap α β) : List (α × β) :=
  map.entries.toList

/--
Merges two multimaps, combining values for shared keys.
-/
def merge (m1 m2 : MultiMap α β) : MultiMap α β :=
  ⟨m1.entries ++ m2.entries⟩

instance : EmptyCollection (MultiMap α β) :=
  ⟨MultiMap.empty⟩

instance : Singleton (α × β) (MultiMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : MultiMap α β).insert a b⟩

instance : Insert (α × β) (MultiMap α β) :=
  ⟨fun ⟨a, b⟩ m => m.insert a b⟩

instance : Union (MultiMap α β) :=
  ⟨merge⟩

instance [Monad m] : ForIn m (MultiMap α β) (α × β) where
  forIn map b f := forIn map.entries b f

end Std.Internal.MultiMap
