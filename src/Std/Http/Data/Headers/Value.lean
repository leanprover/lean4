/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ToString
public import Std.Http.Internal

public section

/-!
# Header Values

This module defines the `Value` type, which represents validated HTTP header values that conform to HTTP
standards.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-values
-/

namespace Std.Http.Header

set_option linter.all true

open Internal

/--
Proposition that asserts all characters in a string are valid for HTTP header values,
and that the first and last characters (if present) are `field-vchar` (not SP/HTAB).

  field-value    = *field-content
  field-content  = field-vchar
                   [ 1*( SP / HTAB / field-vchar ) field-vchar ]

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#section-5.5
-/
abbrev IsValidHeaderValue (s : String) : Prop :=
  let s := s.toList

  s.all Char.fieldContent ∧
  (s.head?.map Char.fieldVchar |>.getD true) ∧
  (s.getLast?.map Char.fieldVchar |>.getD true)

/--
A validated HTTP header value that ensures all characters conform to HTTP standards.
-/
structure Value where
  /--
  The string data.
  -/
  value : String

  /--
  The proof that it's a valid header value.
  -/
  isValidHeaderValue : IsValidHeaderValue value := by decide
deriving BEq, DecidableEq, Repr

instance : Hashable Value where
  hash := Hashable.hash ∘ Value.value

instance : Inhabited Value where
  default := ⟨"", by decide⟩

namespace Value

/--
Attempts to create a `Value` from a `String`, returning `none` if the string contains invalid characters
for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option Value :=
  -- A field value does not include leading or trailing whitespace.
  let val := s.trimAscii.toString

  if h : IsValidHeaderValue val then
    some ⟨val, h⟩
  else
    none

/--
Creates a `Value` from a string, panicking with an error message if the string contains invalid
characters for HTTP header values.
-/
@[expose]
def ofString! (s : String) : Value :=
  match ofString? s with
  | some res => res
  | none => panic! s!"invalid header value: {s.quote}"

/--
Performs a case-insensitive comparison between a `Value` and a `String`. Returns `true` if they match.
-/
@[expose]
def is (s : Value) (h : String) : Bool :=
  s.value.toLower == h.toLower

instance : ToString Value where
  toString v := v.value

end Std.Http.Header.Value
