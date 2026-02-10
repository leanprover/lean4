/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Std.Data.HashMap
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Data.Headers.Basic
public import Std.Internal.Http.Data.Headers.Name
public import Std.Internal.Http.Data.Headers.Value

public section

/-!
# Headers

This module defines the `Headers` type, which represents an collection of HTTP header name-value pairs.
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
A structure for managing HTTP headers as key-value pairs.
-/
structure Headers where

  /--
  The underlying multimap that stores headers.
  -/
  map : MultiMap Header.Name Header.Value
deriving Inhabited, Repr

instance : Membership Header.Name Headers where
  mem s h := h ∈ s.map

instance (name : Header.Name) (h : Headers) : Decidable (name ∈ h) :=
  inferInstanceAs (Decidable (name ∈ h.map))

namespace Headers

/--
Retrieves the first `Header.Value` for the given key.
-/
@[inline]
def get (headers : Headers) (name : Header.Name) (h : name ∈ headers) : Header.Value :=
  headers.map.get name h

/--
Retrieves all `Header.Value` entries for the given key.
-/
@[inline]
def getAll (headers : Headers) (name : Header.Name) (h : name ∈ headers) : Array Header.Value :=
  headers.map.getAll name h

/--
Retrieves all `Header.Value` entries for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getAll? (headers : Headers) (name : Header.Name) : Option (Array Header.Value) :=
  headers.map.getAll? name

/--
Retrieves the first `Header.Value` for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def get? (headers : Headers) (name : Header.Name) : Option Header.Value :=
  headers.map.get? name

/--
Checks if the entry is present in the `Headers`.
-/
@[inline]
def hasEntry (headers : Headers) (name : Header.Name) (value : Header.Value) : Bool :=
  headers.map.data.get? name
  |>.bind (fun x => x.val.find? (· == value))
  |>.isSome

/--
Retrieves the last header value for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getLast? (headers : Headers) (name : Header.Name) : Option Header.Value :=
  headers.map.getLast? name

/--
Like `get?`, but returns a default value if absent.
-/
@[inline]
def getD (headers : Headers) (name : Header.Name) (d : Header.Value) : Header.Value :=
  headers.map.getD name d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! (headers : Headers) (name : Header.Name) : Header.Value :=
  headers.map.get! name

/--
Inserts a new key-value pair into the headers.
-/
@[inline]
def insert (headers : Headers) (key : Header.Name) (value : Header.Value) : Headers :=
  { map := headers.map.insert key value }

/--
Adds a header from string name and value, panicking if either is invalid.
-/
@[inline]
def insert! (headers : Headers) (name : String) (value : String) : Headers :=
  headers.insert (Header.Name.ofString! name) (Header.Value.ofString! value)

/--
Inserts a new key with an array of values.
-/
@[inline]
def insertMany (headers : Headers) (key : Header.Name) (value : Array Header.Value) (p : value.size > 0) : Headers :=
  { map := headers.map.insertMany key value p }

/--
Creates empty headers.
-/
def empty : Headers :=
  { map := ∅ }

/--
Creates headers from a list of key-value pairs.
-/
def ofList (pairs : List (Header.Name × Header.Value)) : Headers :=
  { map := MultiMap.ofList pairs }

/--
Checks if a header with the given name exists.
-/
@[inline]
def contains (headers : Headers) (name : Header.Name) : Bool :=
  headers.map.contains name

/--
Removes a header with the given name.
-/
@[inline]
def erase (headers : Headers) (name : Header.Name) : Headers :=
  { map := headers.map.erase name }

/--
Gets the number of headers.
-/
@[inline]
def size (headers : Headers) : Nat :=
  headers.map.size

/--
Checks if the headers are empty.
-/
@[inline]
def isEmpty (headers : Headers) : Bool :=
  headers.map.isEmpty

/--
Merges two headers, accumulating values for duplicate keys from both.
-/
def merge (headers1 headers2 : Headers) : Headers :=
  { map := headers1.map ∪ headers2.map }

/--
Converts the headers to a list of key-value pairs (flattened). Each header with multiple values produces
multiple pairs.
-/
def toList (headers : Headers) : List (Header.Name × Header.Value) :=
  headers.map.toList

/--
Converts the headers to an array of key-value pairs (flattened). Each header with multiple values
produces multiple pairs.
-/
def toArray (headers : Headers) : Array (Header.Name × Header.Value) :=
  headers.map.toArray

/--
Folds over all key-value pairs in the headers.
-/
def fold (headers : Headers) (init : α) (f : α → Header.Name → Header.Value → α) : α :=
  headers.map.toArray.foldl (fun acc (k, v) => f acc k v) init

/--
Maps a function over all header values, producing new headers.
-/
def mapValues (headers : Headers) (f : Header.Name → Header.Value → Header.Value) : Headers :=
  let pairs := headers.map.toArray.map (fun (k, v) => (k, f k v))
  { map := pairs.foldl (fun acc (k, v) => acc.insert k v) MultiMap.empty }

/--
Filters and maps over header key-value pairs. Returns only the pairs for which the function returns `some`.
-/
def filterMap (headers : Headers) (f : Header.Name → Header.Value → Option Header.Value) : Headers :=
  let pairs := headers.map.toArray.filterMap (fun (k, v) =>
    match f k v with
    | some v' => some (k, v')
    | none => none)
  { map := pairs.foldl (fun acc (k, v) => acc.insert k v) MultiMap.empty }

/--
Filters header key-value pairs, keeping only those that satisfy the predicate.
-/
def filter (headers : Headers) (f : Header.Name → Header.Value → Bool) : Headers :=
  headers.filterMap (fun k v => if f k v then some v else none)

/--
Updates the first value of a header if it exists, or inserts if it doesn't. Replaces all existing values
for that header with the new value.
-/
def update (headers : Headers) (name : Header.Name) (f : Option Header.Value → Header.Value) : Headers :=
  let newValue := f (headers.get? name)
  { map := headers.map.erase name |>.insert name newValue }

instance : ToString Headers where
  toString headers :=
    let pairs := headers.map.toArray.map (fun (k, v) => s!"{k}: {v.value}")
    String.intercalate "\r\n" pairs.toList

instance : Encode .v11 Headers where
  encode buffer headers :=
    headers.fold buffer (fun buf name value =>
      buf.writeString s!"{name}: {value}\r\n")

instance : EmptyCollection Headers :=
  ⟨Headers.empty⟩

instance : Singleton (Header.Name × Header.Value) Headers :=
  ⟨fun ⟨a, b⟩ => (∅ : Headers).insert a b⟩

instance : Insert (Header.Name × Header.Value) Headers :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : Union Headers :=
  ⟨merge⟩

end Std.Http.Headers
