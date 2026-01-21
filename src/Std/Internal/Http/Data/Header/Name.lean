/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Std.Internal.Http.Internal

public section

/-!
# Header Names and Values

This module defines the `Name` and `Value` types, which represent validated
HTTP header names and values that conform to HTTP standards.
-/

namespace Std.Http.Header
open Internal.String

set_option linter.all true

/--
Checks if a character is valid for use in an HTTP header value.
-/
@[expose]
def isValidHeaderChar (c : Char) : Bool :=
  (0x21 ≤  c.val ∧  c.val ≤ 0x7E) ∨ c.val = 0x09 ∨ c.val = 0x20

/--
Proposition that asserts all characters in a string are valid for HTTP header values.
-/
@[expose]
abbrev isValidHeaderValue (s : String) : Prop :=
  s.toList.all isValidHeaderChar

/--
A validated HTTP header value that ensures all characters conform to HTTP standards.
-/
structure Value where
  /--
  The string data
  -/
  value : String

  /--
  The proof that it's a valid header value
  -/
  validHeaderValue : isValidHeaderValue value
deriving BEq, DecidableEq, Repr

namespace Value

instance : Hashable Value := ⟨Hashable.hash ∘ Value.value⟩

instance : Inhabited Value := ⟨⟨"", by native_decide⟩⟩

/--
Creates a new `Value` from a string with an optional proof of validity.
If no proof is provided, it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : s.toList.all isValidHeaderChar := by decide) : Value :=
  ⟨s, h⟩

/--
Attempts to create a `Value` from a `String`, returning `none` if the string
contains invalid characters for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option Value :=
  if h : s.toList.all isValidHeaderChar then
    some ⟨s, h⟩
  else
    none

/--
Creates a `Value` from a string, panicking with an error message if the
string contains invalid characters for HTTP header values.
-/
@[expose]
def ofString! (s : String) : Value :=
  if h : s.toList.all isValidHeaderChar then
    ⟨s, h⟩
  else
    panic! s!"invalid header value: {s.quote}"

/--
Performs a case-insensitive comparison between a `Value` and a `String`.
Returns `true` if they match.
-/
@[expose]
def is (s : Value) (h : String) : Bool :=
  s.value.toLower == h.toLower

instance : ToString Value where
  toString v := v.value

end Value

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
abbrev isNormalForm (s : String) : Prop :=
  s = s.toLower

/--
A validated HTTP header name that ensures all characters conform to HTTP standards.
Header names are case-insensitive according to HTTP specifications.
-/
structure Name where
  /--
  The lowercased normalized header name string.
  -/
  value : String

  /--
  The proof that it's a valid header name
  -/
  validHeaderName : isValidHeaderName value

  /--
  The proof that we stored the header name in normal form
  -/
  normalForm : isNormalForm value
deriving Repr, DecidableEq, BEq

namespace Name

/--
Hash is based on lowercase version for case-insensitive comparison
-/
instance : Hashable Name where
  hash x := Hashable.hash x.value

/--
Equality is case-insensitive
-/
instance : BEq Name where
  beq x y := x.value == y.value

instance : Inhabited Name where default := ⟨"a", ⟨by decide, by decide⟩, by native_decide⟩

/--
Creates a new `Name` from a string with an optional proof of validity.
If no proof is provided, it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : isValidHeaderName s := by decide) (h₁ : isNormalForm s := by native_decide) : Name :=
  ⟨s, h, h₁⟩

/--
Attempts to create a `Name` from a `String`, returning `none` if the string
contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString? (s : String) : Option Name :=
  let val := s.toLower
  if h : isValidHeaderName val ∧ isNormalForm val then
    some ⟨val, h.left, h.right⟩
  else
    none

/--
Creates a `Name` from a string, panicking with an error message if the
string contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString! (s : String) : Name :=
  let val := s.toLower
  if h : isValidHeaderName val ∧ isNormalForm val then
    ⟨val, h.left, h.right⟩
  else
    panic! s!"invalid header name: {s.quote}"

/--
Converts the header name to canonical HTTP title case (e.g., "Content-Type").
-/
@[inline]
def toCanonical (name : Name) : String :=
  let it := name.value.splitOn "-"
    |>.map (·.capitalize)

  String.intercalate "-" it

/--
Performs a case-insensitive comparison between a `Name` and a `String`.
Returns `true` if they match.
-/
@[expose]
def is (name : Name) (s : String) : Bool :=
  name.value == s.toLower

instance : ToString Name where
  toString name := name.toCanonical

end Name

end Std.Http.Header
