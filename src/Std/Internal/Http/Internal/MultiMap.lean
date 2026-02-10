/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
import Init.Data.Int.OfNat
public import Std.Data.HashMap

public section

/-!
# MultiMap

This module defines a generic `MultiMap` type that maps keys to multiple values.
The implementation is optimized for fast lookups and insertions while ensuring
that each key always has at least one associated value.
-/

namespace Std

open Std Internal

set_option linter.all true

/--
A structure for managing key-value pairs where each key can have multiple values.
Invariant: each key must have at least one value.
-/
structure MultiMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where

  /--
  The internal hashmap that stores all the data.
  Each key maps to a non-empty array of values.
  -/
  data : HashMap α { arr : Array β // arr.size > 0 }
deriving Inhabited, Repr

namespace MultiMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

instance : Membership α (MultiMap α β) where
  mem map key := key ∈ map.data

instance (key : α) (map : MultiMap α β) : Decidable (key ∈ map) :=
  inferInstanceAs (Decidable (key ∈ map.data))

/--
Retrieves the first value for the given key.
-/
@[inline]
def get (map : MultiMap α β) (key : α) (h : key ∈ map) : β :=
  let arr := map.data.get key h
  arr.val[0]'(arr.property)

/--
Retrieves all values for the given key.
-/
@[inline]
def getAll (map : MultiMap α β) (key : α) (h : key ∈ map) : Array β :=
  map.data.get key h

/--
Retrieves all values for the given key.
Returns `none` if the key is absent.
-/
@[inline]
def getAll? (map : MultiMap α β) (key : α) : Option (Array β) :=
  if h : key ∈ map then
    some (map.getAll key h)
  else
    none

/--
Retrieves the first value for the given key.
Returns `none` if the key is absent.
-/
@[inline]
def get? (map : MultiMap α β) (key : α) : Option β :=
  if h : key ∈ map then
    some (map.get key h)
  else
    none

/--
Checks if the key-value pair is present in the map.
-/
@[inline]
def hasEntry (map : MultiMap α β) [BEq β] (key : α) (value : β) : Bool :=
  map.data.get? key
  |>.bind (fun x => x.val.find? (· == value))
  |>.isSome

/--
Retrieves the last value for the given key.
Returns `none` if the key is absent.
-/
@[inline]
def getLast? (map : MultiMap α β) (key : α) : Option β :=
  map.data.get? key
  |>.bind (fun x => x.val[x.val.size - 1]?)

/--
Like `get?`, but returns a default value if absent.
-/
@[inline]
def getD (map : MultiMap α β) (key : α) (d : β) : β :=
  map.get? key |>.getD d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! [Inhabited β] (map : MultiMap α β) (key : α) : β :=
  map.get? key |>.get!

/--
Inserts a new key-value pair into the map.
If the key already exists, appends the value to existing values.
-/
@[inline]
def insert (map : MultiMap α β) (key : α) (value : β) : MultiMap α β :=
  let data := map.data.alter key fun
    | some existingValues => some ⟨existingValues.val.push value, by simp⟩
    | none => some ⟨#[value], by simp⟩
  { data }

/--
Inserts a key with an array of values.
-/
@[inline]
def insertMany (map : MultiMap α β) (key : α) (values : Array β) (h : values.size > 0) : MultiMap α β :=
  let data := map.data.alter key fun
    | some existingValues => some ⟨existingValues.val ++ values, by simp; grind⟩
    | none => some ⟨values, h⟩
  { data }

/--
Creates an empty multimap.
-/
def empty : MultiMap α β :=
  { data := ∅ }

/--
Creates a multimap from a list of key-value pairs.
-/
def ofList (pairs : List (α × β)) : MultiMap α β :=
  pairs.foldl (fun acc (k, v) => acc.insert k v) empty

/--
Checks if a key exists in the map.
-/
@[inline]
def contains (map : MultiMap α β) (key : α) : Bool :=
  map.data.contains key

/--
Removes a key and all its values from the map.
-/
@[inline]
def erase (map : MultiMap α β) (key : α) : MultiMap α β :=
  { data := map.data.erase key }

/--
Gets the number of keys in the map.
-/
@[inline]
def size (map : MultiMap α β) : Nat :=
  map.data.size

/--
Checks if the map is empty.
-/
@[inline]
def isEmpty (map : MultiMap α β) : Bool :=
  map.data.isEmpty

/--
Merges two multimaps, with the values of the second appearing after the values of the first for duplicate keys.
-/
def merge (map1 map2 : MultiMap α β) : MultiMap α β :=
  map2.data.fold (fun acc k v => acc.insertMany k v.val v.property) map1

/--
Converts the multimap to an array of key-value pairs (flattened).
-/
def toArray (map : MultiMap α β) : Array (α × β) :=
  map.data.toArray.flatMap (fun (k, vs) => vs.val.map (k, ·))

/--
Converts the multimap to a list of key-value pairs (flattened).
-/
def toList (map : MultiMap α β) : List (α × β) :=
  map.toArray.toList

instance : EmptyCollection (MultiMap α β) :=
  ⟨MultiMap.empty⟩

instance : Singleton (α × β) (MultiMap α β) :=
  ⟨fun ⟨a, b⟩ => (∅ : MultiMap α β).insert a b⟩

instance : Insert (α × β) (MultiMap α β) :=
  ⟨fun ⟨a, b⟩ m => m.insert a b⟩

instance : Union (MultiMap α β) :=
  ⟨merge⟩

end MultiMap
end Std
