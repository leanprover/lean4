/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Data.HashMap
public import Std.Internal.Http.Data.Header.Name
public import Std.Internal.Http.Internal

public section

/-!
# Headers

This module defines the `Headers` type, which represents an efficient collection of HTTP header
name-value pairs. The implementation is optimized for fast lookups and insertions while providing
a convenient interface for managing HTTP headers in both requests and responses.
-/

namespace Std.Http

open Std Internal

set_option linter.all true

/--
A structure for managing HTTP headers as key-value pairs.
-/
structure Headers where
  /--
  The internal hashmap that stores all the data.
  -/
  data : HashMap HeaderName (Array HeaderValue)
  deriving Repr, Inhabited

instance : Membership HeaderName Headers where
  mem h s := s ∈ h.data

instance (name : HeaderName) (h : Headers) : Decidable (name ∈ h) :=
  inferInstanceAs (Decidable (name ∈ h.data))

namespace Headers

/--
Proposition that a string corresponds to a valid header name present in the headers.
-/
abbrev In (s : String) (h : Headers) : Prop :=
  match HeaderName.ofString? s with
  | some name => name ∈ h
  | none => False

instance {s : String} {h : Headers} : Decidable (In s h) := by
  unfold In
  cases headerName : HeaderName.ofString? s
  all_goals exact inferInstance

/--
Retrieves the `HeaderValue` for the given key.
-/
@[inline]
def get (headers : Headers) (name : HeaderName) (h : name ∈ headers) : HeaderValue :=
  headers.data.get name h
  |> HeaderValue.joinCommaSep

/--
Retrieves all `HeaderValue` entries for the given key.
-/
@[inline]
def getAll (headers : Headers) (name : HeaderName) (h : name ∈ headers) : Array HeaderValue :=
  headers.data.get name h

/--
Retrieves all `HeaderValue` entries for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getAll? (headers : Headers) (name : HeaderName) : Option (Array HeaderValue) :=
  if h : name ∈ headers then
    some (headers.getAll name h)
  else
    none

/--
Retrieves the `HeaderValue` for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def get? (headers : Headers) (name : HeaderName) : Option HeaderValue :=
  if h : name ∈ headers then
    some (headers.get name h)
  else
    none

/--
Checks if the entry is present in the `Headers`.
-/
@[inline]
def hasEntry (headers : Headers) (name : HeaderName) (value : String) : Bool :=
  headers.data.get? name
  |>.bind (·.find? (·.is value))
  |>.isSome

/--
Retrieves the last header value for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getLast? (headers : Headers) (name : HeaderName) : Option HeaderValue :=
  headers.data.get? name
  |>.bind (fun x => x[x.size - 1]?)

/--
Like `get?`, but returns a default value if absent.
-/
@[inline]
def getD (headers : Headers) (name : HeaderName) (d : HeaderValue) : HeaderValue :=
  headers.get? name |>.getD d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! (headers : Headers) (name : HeaderName) : HeaderValue :=
  headers.get? name |>.get!

/--
Inserts a new key-value pair into the headers.
-/
@[inline]
def insert (headers : Headers) (key : HeaderName) (value : HeaderValue) : Headers :=
  if let some headerValue := headers.data.get? key then
    { data := headers.data.insert key (headerValue.push value) }
  else
    { data := headers.data.insert key #[value] }

/--
Inserts a new key with an array of values.
-/
@[inline]
def insertMany (headers : Headers) (key : HeaderName) (value : Array HeaderValue) : Headers :=
  if let some headerValue := headers.data.get? key then
    { data := headers.data.insert key (headerValue ++ value) }
  else
    { data := headers.data.insert key value }

/--
Creates empty headers.
-/
def empty : Headers :=
  { data := ∅ }

/--
Creates headers from a list of key-value pairs.
-/
def ofList (pairs : List (HeaderName × HeaderValue)) : Headers :=
  { data := HashMap.ofList (pairs.map (fun (k, v) => (k, #[v]))) }

/--
Checks if a header with the given name exists.
-/
@[inline]
def contains (headers : Headers) (name : HeaderName) : Bool :=
  headers.data.contains name

/--
Removes a header with the given name.
-/
@[inline]
def erase (headers : Headers) (name : HeaderName) : Headers :=
  { data := headers.data.erase name }

/--
Gets the number of headers.
-/
@[inline]
def size (headers : Headers) : Nat :=
  headers.data.size

/--
Checks if the headers are empty.
-/
@[inline]
def isEmpty (headers : Headers) : Bool :=
  headers.data.isEmpty

/--
Merges two headers, with the second taking precedence for duplicate keys.
-/
def merge (headers1 headers2 : Headers) : Headers :=
  headers2.data.fold (fun acc k v => acc.insertMany k v) headers1

instance : ToString Headers where
  toString headers :=
    let pairs := headers.data.toArray.flatMap (fun (k, vs) => vs.map (k, ·))
    let pairs := pairs.map (fun (k, vs) => s!"{k}: {vs.value}")
    String.intercalate "\r\n" pairs.toList

instance : Encode .v11 Headers where
  encode buffer := buffer.writeString ∘ toString

instance : EmptyCollection Headers := ⟨Headers.empty⟩

instance : Singleton (HeaderName × HeaderValue) Headers := ⟨fun ⟨a, b⟩ => (∅ : Headers).insert a b⟩

instance : Insert (HeaderName × HeaderValue) Headers := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : Union Headers := ⟨merge⟩

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

theorem in_implies_valid (h : In name headers) : isValidHeaderName name :=
  if h₀ : isValidHeaderName name then h₀ else by
    unfold In HeaderName.ofString? at h
    simp [h₀] at h

theorem mem_implies_valid (name : String) (inList : name ∈ list) (hasAll : HasAll headers list) : isValidHeaderName name :=
  in_implies_valid (in_of_hasall name inList hasAll)

theorem in_implies_mem (h : In nn headers) : ∃p : (isValidHeaderName nn), HeaderName.mk nn p ∈ headers := by
  simp [In, HeaderName.ofString?] at h
  if h2 : isValidHeaderName nn then
    simp [eq_true h2] at h
    exact ⟨_, h⟩
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
def get (hasAll : HasAll headers l) (name : String) (h : (name ∈ l) := by get_elem_tactic) : HeaderValue :=
  let h2 := in_implies_mem (in_of_hasall name h hasAll)
  headers.get (HeaderName.mk name h2.choose) h2.choose_spec

/--
Gets all values of a header by name.
-/
def getAll (hasAll : HasAll headers l) (name : String) (h : (name ∈ l) := by get_elem_tactic) : Array HeaderValue :=
  let h2 := in_implies_mem (in_of_hasall name h hasAll)
  headers.getAll (HeaderName.mk name h2.choose) h2.choose_spec

instance : Decidable (HasAll h l) := decidable

end HasAll
end Std.Http.Headers
