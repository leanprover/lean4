/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Slice
public import Std.Data.HashMap
public import Std.Data.HashSet
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
Checks if a character is valid for use in an HTTP header value.
Valid characters include:
- Characters with values > 0x7F (extended ASCII)
- Tab character (0x09)
- Space character (0x20)
- Printable ASCII characters (0x21 to 0x7E)
-/
@[expose]
def isValidHeaderCharNode (c : Char) : Bool :=
  (0x21 ≤  c.val ∧  c.val ≤ 0x7E) ∨ c.val = 0x09 ∨ c.val = 0x20

/--
Proposition that asserts all characters in a string are valid for HTTP header values.
-/
@[expose]
abbrev isValidHeaderValue (s : String) : Prop :=
  s.data.all isValidHeaderCharNode

/--
A validated HTTP header value that ensures all characters conform to HTTP standards.
-/
structure HeaderValue where
  /--
  The string data
  -/
  value : String

  /--
  The proof that it's a valid header value
  -/
  validHeaderValue : isValidHeaderValue value
deriving BEq, Repr

namespace HeaderValue

instance : Hashable HeaderValue where
  hash x := Hashable.hash x.value

instance : Inhabited HeaderValue where default := ⟨"", by decide⟩

/--
Creates a new `HeaderValue` from a string with an optional proof of validity.
If no proof is provided, it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : s.data.all isValidHeaderCharNode := by decide) : HeaderValue :=
  ⟨s, h⟩

/--
Attempts to create a `HeaderValue` from a `String`, returning `none` if the string
contains invalid characters for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option HeaderValue :=
  if h : s.data.all isValidHeaderCharNode then
    some ⟨s, h⟩
  else
    none

/--
Creates a `HeaderValue` from a string, panicking with an error message if the
string contains invalid characters for HTTP header values.
-/
@[expose]
def ofString! (s : String) : HeaderValue :=
  if h : s.data.all isValidHeaderCharNode then
    ⟨s, h⟩
  else
    panic! s!"invalid header value: {s.quote}"

/--
Performs a case-insensitive comparison between a `HeaderValue` and a `String`.
Returns `true` if they match.
-/
@[expose]
def is (s : HeaderValue) (h : String) : Bool :=
  s.value.toLower == h.toLower

/--
Concatenates two `HeaderValue` instances, preserving the validity guarantee.
-/
def append (l : HeaderValue) (r : HeaderValue) : HeaderValue := by
  refine ⟨l.value ++ r.value, ?_⟩
  unfold isValidHeaderValue
  rw [String.data_append]
  rw [List.all_append]
  rw [Bool.and_eq_true]
  constructor
  · exact l.validHeaderValue
  · exact r.validHeaderValue

instance : HAppend HeaderValue HeaderValue HeaderValue where
  hAppend := HeaderValue.append

/--
Joins an array of `HeaderValue` instances with comma-space separation.
Returns a single `HeaderValue` containing all values joined together.
If the array is empty, returns an empty `HeaderValue`.
-/
def joinCommaSep (x : Array HeaderValue) : HeaderValue :=
  if h : 0 < x.size then
    let first := x[0]'h
    let rest := x[1...*]
    rest.foldl (· ++ HeaderValue.new ", " ++ ·) first
  else
    .new ""

end HeaderValue

/--
A structure for managing HTTP headers as key-value pairs.
-/
structure Headers where
  /--
  The internal hashmap that stores all the data.
  -/
  data : HashMap String (String × (Array HeaderValue))

deriving Repr, Inhabited

namespace Headers

/--
Tries to retrieve the `HeaderValue` for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def get? (headers : Headers) (name : String) : Option HeaderValue :=
  headers.data.get? name.toLower
  |>.map (.joinCommaSep ∘ Prod.snd)

/--
Tries to check if the entry is present in the `Headers`
-/
@[inline]
def hasEntry (headers : Headers) (name : String) (value : String) : Bool :=
  headers.data.get? name.toLower
  |>.map Prod.snd
  |>.bind (·.find? (·.is value))
  |>.isSome

/--
Tries to retrieve the last header value for the given key.
Returns `none` if the header is absent.
-/
@[inline]
def getLast? (headers : Headers) (name : String) : Option HeaderValue :=
  headers.data.get? name.toLower
  |>.bind (fun x => let arr := Prod.snd x; arr[arr.size - 1]?)


/--
Like `get?`, but returns an empty HashSet if absent.
-/
@[inline]
def getD (headers : Headers) (name : String) (d : HeaderValue) : HeaderValue :=
  headers.get? name |>.getD d

/--
Like `get?`, but panics if absent.
-/
@[inline]
def get! (headers : Headers) (name : String) : HeaderValue :=
  headers.get? name |>.get!

/--
Inserts a new key-value pair into the headers.
-/
@[inline]
def insert (headers : Headers) (name : String) (value : HeaderValue) : Headers :=
  let key := name.toLower

  if let some (_, headerValue) := headers.data.get? key then
    { data := headers.data.insert key (name, headerValue.push value) }
  else
    { data := headers.data.insert key (name, #[value]) }

/--
Inserts a new key with an array of values.
-/
@[inline]
def insertMany (headers : Headers) (name : String) (value : Array HeaderValue) : Headers :=
  let key := name.toLower

  if let some (_, headerValue) := headers.data.get? key then
    { data := headers.data.insert key (name, headerValue ++ value) }
  else
    { data := headers.data.insert key (name, value) }

/--
Creates empty headers.
-/
def empty : Headers :=
  { data := ∅ }

/--
Creates headers from a list of key-value pairs.
-/
def ofList (pairs : List (String × HeaderValue)) : Headers :=
  { data := HashMap.ofList (pairs.map (fun (k, v) => (k.toLower, (k, #[v])))) }

/--
Checks if a header with the given name exists.
-/
@[inline]
def contains (headers : Headers) (name : String) : Bool :=
  headers.data.contains name.toLower

/--
Removes a header with the given name.
-/
@[inline]
def erase (headers : Headers) (name : String) : Headers :=
  { data := headers.data.erase name.toLower }

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
  headers2.data.fold (fun acc k (_, v) => acc.insertMany k v) headers1

instance : ToString Headers where
  toString headers :=
    let pairs := headers.data.toList.map (fun (_, (k, vs)) => s!"{k}: {HeaderValue.joinCommaSep vs |>.value}")
    String.intercalate "\r\n" pairs

instance : Encode .v11 Headers where
  encode buffer := buffer.writeString ∘ toString

end Std.Http.Headers
