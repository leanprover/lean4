/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ToString
public import Std.Http.Internal
public import Init.Data.String.Search
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import Init.Data.String.Lemmas.Search

public section

/-!
# Header Values

This module defines the `Value` type, which represents validated HTTP header values that conform to HTTP
standards.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-values
-/

namespace Std.Http.Header

set_option linter.all true

open Std.Http.Internal

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
Compiled implementation of `isValid`. Field-value characters are ASCII, and neither the first nor the
last byte of a non-ASCII character is a `field-vchar`, so the check can run on UTF-8 bytes.
-/
def isValidImpl (s : String) : Bool :=
  if h : 0 < s.utf8ByteSize then
    Char.fieldVchar (Char.ofUInt8 (s.getUTF8Byte ⟨0⟩ h)) &&
    Char.fieldVchar (Char.ofUInt8 (s.getUTF8Byte ⟨s.utf8ByteSize - 1⟩ (by
      show s.utf8ByteSize - 1 < s.utf8ByteSize
      omega))) &&
    go 0
  else
    true
where
  /-- Checks the bytes from index `i` on. -/
  go (i : Nat) : Bool :=
    if h : i < s.utf8ByteSize then
      Char.fieldContent (Char.ofUInt8 (s.getUTF8Byte ⟨i⟩ h)) && go (i + 1)
    else
      true
  termination_by s.utf8ByteSize - i

/--
Decides `IsValidHeaderValue`.
-/
@[implemented_by isValidImpl]
def isValid (s : String) : Bool :=
  decide (IsValidHeaderValue s)

theorem of_isValid {s : String} (h : isValid s = true) : IsValidHeaderValue s :=
  of_decide_eq_true h

/--
Creates a `Value` from a string that has no leading or trailing whitespace, returning `none` if it
contains invalid characters.
-/
@[inline]
def ofTrimmed? (s : String) : Option Value :=
  if h : isValid s then
    some ⟨s, of_decide_eq_true h⟩
  else
    none

/--
Attempts to create a `Value` from a `String`, returning `none` if the string contains invalid characters
for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option Value :=
  ofTrimmed? (if isAsciiTrimmed s then s else s.trimAscii.toString)

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
