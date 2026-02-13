/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Init.Data.ToString
public import Std.Internal.Http.Internal

public section

/-!
# Header Values

This module defines the `Value` type, which represent validated HTTP header values that conform to HTTP
standards.
-/

namespace Std.Http.Header

set_option linter.all true

open Internal

/--
Checks if a character is valid for use in an HTTP header value.
-/
abbrev isValidHeaderChar (c : Char) : Bool :=
  (' ' ≤ c ∧ c ≤ '~') ∨ c = '\t'

/--
Proposition that asserts all characters in a string are valid for HTTP header values.
-/
abbrev IsValidHeaderValue (s : String) : Prop :=
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
  validHeaderValue : IsValidHeaderValue value := by decide
deriving BEq, DecidableEq, Repr

instance : Hashable Value where
  hash := Hashable.hash ∘ Value.value

instance : Inhabited Value where
  default := ⟨"_", by decide⟩

namespace Value

/--
Attempts to create a `Value` from a `String`, returning `none` if the string contains invalid characters
for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option Value :=
  if h : IsValidHeaderValue s then
    some ⟨s, h⟩
  else
    none

/--
Creates a `Value` from a string, panicking with an error message if the string contains invalid
characters for HTTP header values.
-/
@[expose]
def ofString! (s : String) : Value :=
  if h : IsValidHeaderValue s then
    ⟨s, h⟩
  else
    panic! s!"invalid header value: {s.quote}"

/--
Performs a case-insensitive comparison between a `Value` and a `String`. Returns `true` if they match.
-/
@[expose]
def is (s : Value) (h : String) : Bool :=
  s.value.toLower == h.toLower

instance : ToString Value where
  toString v := v.value

/--
Standard close header value
-/
def close : Header.Value := .mk "close"

/--
Standard chunked header value
-/
def chunked : Header.Value := .mk "chunked"

end Std.Http.Header.Value
