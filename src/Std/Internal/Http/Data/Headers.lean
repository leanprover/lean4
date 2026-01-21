/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data.Header.Basic
public import Std.Internal.Http.Internal

public section

/-!
# Headers

This module defines the `Headers` type, which represents an efficient collection of HTTP header
name-value pairs. The implementation is built on top of the generic `MultiMap` structure,
optimized for fast lookups and insertions while providing a convenient interface for managing
HTTP headers in both requests and responses.
-/

namespace Std.Http

open Std Internal

set_option linter.all true

/--
A structure for managing HTTP headers as key-value pairs.
Built on top of `MultiMap` for efficient multi-value header support.
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
Proposition that a string corresponds to a valid header name present in the headers.
-/
abbrev In (s : String) (h : Headers) : Prop :=
  match Header.Name.ofString? s with
  | some name => name ∈ h
  | none => False

instance {s : String} {h : Headers} : Decidable (In s h) := by
  unfold In
  cases headerName : Header.Name.ofString? s
  all_goals exact inferInstance

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
Merges two headers, with the second taking precedence for duplicate keys.
-/
def merge (headers1 headers2 : Headers) : Headers :=
  { map := headers1.map ∪ headers2.map }

/--
Converts the headers to a list of key-value pairs (flattened).
Each header with multiple values produces multiple pairs.
-/
def toList (headers : Headers) : List (Header.Name × Header.Value) :=
  headers.map.toList

/--
Converts the headers to an array of key-value pairs (flattened).
Each header with multiple values produces multiple pairs.
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
Filters and maps over header key-value pairs.
Returns only the pairs for which the function returns `some`.
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
Updates the first value of a header if it exists, or inserts if it doesn't.
Replaces all existing values for that header with the new value.
-/
def update (headers : Headers) (name : Header.Name) (f : Option Header.Value → Header.Value) : Headers :=
  let newValue := f (headers.get? name)
  { map := headers.map.erase name |>.insert name newValue }

instance : ToString Headers where
  toString headers :=
    let pairs := headers.map.toArray.map (fun (k, v) => s!"{k}: {v.value}")
    String.intercalate "\r\n" pairs.toList

instance : Encode .v11 Headers where
  encode buffer := buffer.writeString ∘ toString

instance : EmptyCollection Headers :=
  ⟨Headers.empty⟩

instance : Singleton (Header.Name × Header.Value) Headers :=
  ⟨fun ⟨a, b⟩ => (∅ : Headers).insert a b⟩

instance : Insert (Header.Name × Header.Value) Headers :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : Union Headers :=
  ⟨merge⟩

/--
Proposition that all strings in a list are present in the headers.
-/
inductive HasAll : (h : Headers) → (l : List String) → Prop where
  /--
  The empty list is trivially present in any headers.
  -/
  | nil : HasAll h []

  /--
  If a string is in headers and the rest of the list satisfies HasAll,
  then the whole list satisfies HasAll.
  -/
  | cons (member : In s h) (tail : HasAll h rest) : HasAll h (s :: rest)

namespace HasAll

theorem in_of_hasall (name : String) (inList : name ∈ list) (hasAll : HasAll headers list) : In name headers :=
  match hasAll with
  | .nil => by contradiction
  | @HasAll.cons s _ _ member tail =>
    if eq : s = name then
      eq ▸ member
    else
      in_of_hasall name (List.mem_of_ne_of_mem (Ne.intro (fun x => eq x.symm)) inList) tail

theorem in_implies_valid (h : In name headers) : Header.isValidHeaderName name.toLower :=
  if h₀ : Header.isValidHeaderName name.toLower then h₀ else by
    unfold In Header.Name.ofString? at h
    simp [h₀] at h

theorem mem_implies_valid (name : String) (inList : name ∈ list) (hasAll : HasAll headers list) : Header.isValidHeaderName name.toLower :=
  in_implies_valid (in_of_hasall name inList hasAll)

theorem in_implies_mem (h : In nn headers) : ∃p : (Header.isValidHeaderName nn.toLower ∧ Header.isNormalForm nn.toLower), Header.Name.mk nn.toLower p.left p.right ∈ headers := by
  simp [In, Header.Name.ofString?] at h
  if h2 : Header.isValidHeaderName nn.toLower ∧ Header.isNormalForm nn.toLower then
    simp [eq_true h2] at h
    exact ⟨h2, h⟩
  else
    simp [eq_false h2] at h

theorem tail (hasAll : HasAll headers (h :: t)) : HasAll headers t := by
  cases hasAll with
  | cons _ tail => exact tail

theorem head : (hasAll : HasAll headers (h :: t)) → In h headers
  | cons member _ => member

/--
Decision procedure for `HasAll`.
-/
def decidable : Decidable (HasAll h l) :=
  match l with
  | [] => isTrue HasAll.nil
  | head :: tail =>
    if headMember : In head h then
      match @decidable h tail with
      | isTrue tailHasAll => Decidable.isTrue (HasAll.cons headMember tailHasAll)
      | isFalse notTailHasAll => Decidable.isFalse fun hasAll => notTailHasAll hasAll.tail
    else
      Decidable.isFalse fun hasAll => headMember hasAll.head

/--
Gets the value of a header by name.
-/
def get (hasAll : HasAll headers l) (name : String) (h : (name ∈ l) := by get_elem_tactic) : Header.Value :=
  let h2 := in_implies_mem (in_of_hasall name h hasAll)
  headers.get (Header.Name.mk name.toLower h2.choose.left h2.choose.right) h2.choose_spec

/--
Gets all values of a header by name.
-/
def getAll (hasAll : HasAll headers l) (name : String) (h : (name ∈ l) := by get_elem_tactic) : Array Header.Value :=
  let h2 := in_implies_mem (in_of_hasall name h hasAll)
  headers.getAll (Header.Name.mk name.toLower h2.choose.left h2.choose.right) h2.choose_spec

instance : Decidable (HasAll h l) := decidable

end HasAll
end Headers
end Std.Http
