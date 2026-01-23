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
def isValidHeaderChar (c : Char) : Bool :=
  ('!' ≤ c ∧ c ≤ '~') ∨ c = '\t' ∨ c = ' '

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
  validHeaderValue : IsValidHeaderValue value
deriving BEq, DecidableEq, Repr

instance : Hashable Value where
  hash := Hashable.hash ∘ Value.value

instance : Inhabited Value where
  default := ⟨"", by decide⟩

namespace Value

/--
Creates a new `Value` from a string with an optional proof of validity. If no proof is provided,
it attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : s.toList.all isValidHeaderChar := by decide) : Value :=
  ⟨s, h⟩

/--
Attempts to create a `Value` from a `String`, returning `none` if the string contains invalid characters
for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option Value :=
  if h : s.toList.all isValidHeaderChar then
    some ⟨s, h⟩
  else
    none

/--
Creates a `Value` from a string, panicking with an error message if the string contains invalid
characters for HTTP header values.
-/
@[expose]
def ofString! (s : String) : Value :=
  if h : s.toList.all isValidHeaderChar then
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

end Std.Http.Header.Value
