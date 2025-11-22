/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Slice
public import Init.Data.String
public import Std.Data.HashMap
public import Std.Data.HashSet

public section

/-!
# Header Names and Values

This module defines the `HeaderName` and `HeaderValue` types, which represent validated
HTTP header names and values that conform to HTTP standards.
-/

namespace Std.Http

set_option linter.all true

/--
Checks if a character is valid for use in an HTTP header value.
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
def append (l : HeaderValue) (r : HeaderValue) : HeaderValue :=
  ⟨l.value ++ r.value, ?_⟩
where finally
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

instance : ToString HeaderValue where
  toString v := v.value

end HeaderValue

/--
Checks if a character is valid for use in an HTTP header name.
-/
@[expose]
def isValidHeaderNameChar (c : Char) : Bool :=
  let v := c.val

  if v < 0x21 || v > 0x7E then
    false
  else
    v != 0x22 && v != 0x28 && v != 0x29 && v != 0x2C && v != 0x3B
    && v != 0x5B && v != 0x5D && v != 0x7B && v != 0x7D

/--
Proposition that asserts all characters in a string are valid for HTTP header names.
-/
@[expose]
abbrev isValidHeaderName (s : String) : Prop :=
  s.data.all isValidHeaderNameChar ∧ !s.data.isEmpty

/--
A validated HTTP header name that ensures all characters conform to HTTP standards.
Header names are case-insensitive according to HTTP specifications.
-/
structure HeaderName where
  /--
  The original case-preserved string
  -/
  value : String

  /--
  The proof that it's a valid header name
  -/
  validHeaderName : isValidHeaderName value
deriving Repr

namespace HeaderName

/--
Hash is based on lowercase version for case-insensitive comparison
-/
instance : Hashable HeaderName where
  hash x := Hashable.hash x.value.toLower

/--
Equality is case-insensitive
-/
instance : BEq HeaderName where
  beq x y := x.value.toLower == y.value.toLower

instance : Inhabited HeaderName where default := ⟨"a", ⟨by decide, by decide⟩⟩

/--
Creates a new `HeaderName` from a string with an optional proof of validity.
If no proof is provided, it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : isValidHeaderName s := by decide) : HeaderName :=
  ⟨s, h⟩

/--
Attempts to create a `HeaderName` from a `String`, returning `none` if the string
contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString? (s : String) : Option HeaderName :=
  if h : isValidHeaderName s then
    some ⟨s, h⟩
  else
    none

/--
Creates a `HeaderName` from a string, panicking with an error message if the
string contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString! (s : String) : HeaderName :=
  if h : isValidHeaderName s then
    ⟨s, h⟩
  else
    panic! s!"invalid header name: {s.quote}"

/--
Gets the lowercase version of the header name for case-insensitive operations.
-/
@[inline]
def toLower (name : HeaderName) : String :=
  name.value.toLower

/--
Performs a case-insensitive comparison between a `HeaderName` and a `String`.
Returns `true` if they match.
-/
@[expose]
def is (name : HeaderName) (s : String) : Bool :=
  name.value.toLower == s.toLower

instance : ToString HeaderName where
  toString name := name.value

end HeaderName

end Std.Http
