/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String

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
  s.toList.all isValidHeaderCharNode

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
deriving BEq, DecidableEq, Repr

namespace HeaderValue

instance : Hashable HeaderValue := ⟨Hashable.hash ∘ HeaderValue.value⟩

instance : Inhabited HeaderValue := ⟨⟨"", by native_decide⟩⟩

/--
Creates a new `HeaderValue` from a string with an optional proof of validity.
If no proof is provided, it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : s.toList.all isValidHeaderCharNode := by decide) : HeaderValue :=
  ⟨s, h⟩

/--
Attempts to create a `HeaderValue` from a `String`, returning `none` if the string
contains invalid characters for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option HeaderValue :=
  if h : s.toList.all isValidHeaderCharNode then
    some ⟨s, h⟩
  else
    none

/--
Creates a `HeaderValue` from a string, panicking with an error message if the
string contains invalid characters for HTTP header values.
-/
@[expose]
def ofString! (s : String) : HeaderValue :=
  if h : s.toList.all isValidHeaderCharNode then
    ⟨s, h⟩
  else
    panic! s!"invalid header value: {s.quote}"

/--
Performs a case-insensitive comparison between a `HeaderValue` and a `String`.
Returns `true` if they match.
-/
@[expose]
def is (s : HeaderValue) (h : String) : Bool :=
  s.value == h.toLower

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
  s.toList.all isValidHeaderNameChar ∧ !s.toList.isEmpty

/--
Proposition that a header name is in the internal normal form, meaning it has been
normalized by lowercasing.
-/
@[expose]
abbrev isNormalForm (s: String) : Prop :=
  s = s.toLower

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

  /--
  The proof that we stored the header name in normal form
  -/
  normalform: isNormalForm value
deriving Repr, DecidableEq, BEq, Repr

namespace HeaderName

/--
Hash is based on lowercase version for case-insensitive comparison
-/
instance : Hashable HeaderName where
  hash x := Hashable.hash x.value

/--
Equality is case-insensitive
-/
instance : BEq HeaderName where
  beq x y := x.value == y.value

instance : Inhabited HeaderName where default := ⟨"a", ⟨by decide, by decide⟩, by native_decide⟩

/--
Creates a new `HeaderName` from a string with an optional proof of validity.
If no proof is provided, it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : isValidHeaderName s := by decide) (h₁ : isNormalForm s := by native_decide) : HeaderName :=
  ⟨s, h, h₁⟩

/--
Attempts to create a `HeaderName` from a `String`, returning `none` if the string
contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString? (s : String) : Option HeaderName :=
  let val := s.toLower
  if h : isValidHeaderName val ∧ isNormalForm val then
    some ⟨val, h.left, h.right⟩
  else
    none

/--
Creates a `HeaderName` from a string, panicking with an error message if the
string contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString! (s : String) : HeaderName :=
  let val := s.toLower
  if h : isValidHeaderName val ∧ isNormalForm val then
    ⟨val, h.left, h.right⟩
  else
    panic! s!"invalid header name: {s.quote}"

/--
Gets the lowercase version of the header name for case-insensitive operations.
-/
@[inline]
def toCanonical (name : HeaderName) : String :=
  let it := name.value.split '-'
    |>.map (·.toString.capitalize)

  String.intercalate "-" it.toList

/--
Performs a case-insensitive comparison between a `HeaderName` and a `String`.
Returns `true` if they match.
-/
@[expose]
def is (name : HeaderName) (s : String) : Bool :=
  name.value == s.toLower

instance : ToString HeaderName where
  toString name := name.toCanonical

end HeaderName

end Std.Http
