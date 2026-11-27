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
public import Std.Http.Data.Headers.Bytes
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import Init.Data.String.Lemmas.Search
import Init.Data.List.ToArray
import Init.Data.Array.Lemmas
import Init.Data.Option.Lemmas

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
Attempts to create a `Value` from a `String`, returning `none` if the string contains invalid characters
for HTTP header values.
-/
@[expose]
def ofString? (s : String) : Option Value :=
  -- A field value does not include leading or trailing whitespace; trim only when there is some.
  let val :=
    if s.front?.all (!·.isWhitespace) && s.back?.all (!·.isWhitespace) then s
    else s.trimAscii.toString
  if h : isFieldValue val then
    some ⟨val, by simp only [isFieldValue, Bool.and_eq_true] at h; exact ⟨h.1.1, h.1.2, h.2⟩⟩
  else
    none

/--
Creates a `Value` from bytes that are all ASCII, without whitespace at either end: `none` unless
every byte is field content and the first and last are field-vchars. For such bytes it gives
`ofString?` of the string they encode.
-/
def ofAsciiBytes? (b : ByteArray) : Option Value :=
  if ha : b.data.all (· < 128) then
    if h : b.data.all (fun x => Char.fieldContent (Char.ofUInt8 x)) &&
        ((b.data[0]?).map (Char.fieldVchar ∘ Char.ofUInt8) |>.getD true) &&
        ((b.data.back?).map (Char.fieldVchar ∘ Char.ofUInt8) |>.getD true) then
      some ⟨ofAsciiBytes b ha, by
        have hb : b.data.back? = b.data.toList.getLast? := by
          rw [← List.back?_toArray, Array.toArray_toList]
        simp only [Bool.and_eq_true] at h
        simp only [IsValidHeaderValue, toList_ofAsciiBytes, List.all_map, List.getLast?_map,
          Array.all_toList, List.head?_eq_getElem?, ← hb]
        exact ⟨by simpa using h.1.1, by simpa using h.1.2, by simpa [Option.map_map] using h.2⟩⟩
    else
      none
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

instance : Encode .v11 Value where
  encode out v := out ++ v.value

end Std.Http.Header.Value
