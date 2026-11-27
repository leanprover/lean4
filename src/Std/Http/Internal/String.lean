/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import Init.Grind
public import Init.Data.String.TakeDrop
public import Std.Http.Internal.Char
import Init.Data.String.Csimp
import Init.Data.String.Lemmas.Search
import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Lemmas
import Init.Data.List.ToArray
import Init.Data.UInt.Lemmas

public section


/-!
# Internal String Helpers

Shared string utilities for HTTP: token validation and quoted-string encoding/decoding for header
parameter values and chunk extensions.
-/

namespace Std.Http.Internal

open Std.Http.Internal.Char

set_option linter.all true

/--
Core character quoting used by `quoteHttpString`.

Emits `qdtext` characters directly and `"` / `\\` as `quoted-pair`.
The proof `h₀ : quotedStringChar c` guarantees the impossible branch is unreachable.
-/
def quoteCore (c : Char) (h₀ : quotedStringChar c) : String :=
  if h : qdtext c then
    .singleton c
  else if h₁ : c = '\"' || c = '\\' then
    .append "\\" (.singleton c)
  else
    absurd h₀ (not_quotedStringChar_of_not_qdtext_not_dquote_backslash _ (quotedStringChar_lt_0x80 h₀) ⟨h, h₁⟩)

/--
Quotes `s` as an HTTP `quoted-string`: `DQUOTE *( qdtext / quoted-pair ) DQUOTE`.

If every character is a `tchar` and the string is non-empty, the string is returned as-is (it is
already a valid token). Otherwise the string is wrapped in double quotes, escaping `"` and `\`
as `quoted-pair`.

Requires a proof that every character passes `quotedStringChar`.
-/
@[expose]
def quoteHttpString (s : String) (h : s.toList.all quotedStringChar) : String :=
  let sl := s.toList.attach

  if sl.all (tchar ·.val) ∧ ¬sl.isEmpty then
    s
  else
    (.append
      (sl.foldl (fun acc x =>
        .append acc (quoteCore x.val (List.all_eq_true.mp h x.val x.2))) "\"")
      "\"")

/--
Attempts to quote `s` as an HTTP `quoted-string`.

Returns `some` with the quoted result when every character passes `quotedStringChar`, or `none`
when any character cannot be represented by the grammar.
-/
def quoteHttpString? (s : String) : Option String :=
  if h : s.toList.all quotedStringChar then
    some <| quoteHttpString s h
  else
    none

/--
Quotes `s` as an HTTP `quoted-string`, panicking if `s` contains characters that cannot be
represented by `qdtext`/`quoted-pair`.
-/
def quoteHttpString! (s : String) : String :=
  match quoteHttpString? s with
  | some res => res
  | none => panic! "invalid HTTP quoted-string content"

private inductive UnquoteState where
  | start
  | valid (escaped : Bool) (acc : String)
  | done (result : String)
  | invalid

/--
Parses an HTTP `quoted-string`, returning the unescaped content when valid.
-/
def unquoteHttpString? (s : String) : Option String :=
  if s.startsWith '"' then
    match s.foldl (fun (st : UnquoteState) c =>
      match st with
      | .start =>
          if c == '"' then .valid false "" else .invalid
      | .valid false acc =>
          if c == '\\' then .valid true acc
          else if c == '"' then .done acc
          else if qdtext c then .valid false (acc.push c)
          else .invalid
      | .valid true acc =>
          if quotedPairChar c then .valid false (acc.push c)
          else .invalid
      | .done _ | .invalid => .invalid) .start with
    | .done result => some result
    | _ => none
  else if s.all Char.tchar then
    some s
  else
    none

/--
Checks whether a string is a valid non-empty HTTP token.
-/
@[expose]
noncomputable def isToken (s : String) : Bool :=
  let s := s.toList
  ¬s.isEmpty ∧ s.all Char.tchar

/--
Runtime implementation of `isToken` that avoids materializing `toList`.
-/
def isTokenImpl (s : String) : Bool :=
  !s.isEmpty && s.all Char.tchar

/--
Use `isTokenImpl` at run time while leaving the list-based version for proofs.
-/
@[csimp]
theorem isToken_eq_isTokenImpl : isToken = isTokenImpl := by
  funext s
  rw [Bool.eq_iff_iff]
  simp [isToken, isTokenImpl, String.all_bool_eq, List.isEmpty_iff]

/--
Checks whether a string is a valid HTTP field value (RFC 9110 §5.5): field content throughout, with a
visible character at each end.
-/
@[expose]
noncomputable def isFieldValue (s : String) : Bool :=
  let s := s.toList
  s.all Char.fieldContent && (s.head?.map Char.fieldVchar |>.getD true) &&
    (s.getLast?.map Char.fieldVchar |>.getD true)

/--
Runtime implementation of `isFieldValue` that avoids materializing `toList`.
-/
def isFieldValueImpl (s : String) : Bool :=
  s.all Char.fieldContent && (s.front?.map Char.fieldVchar |>.getD true) &&
    (s.back?.map Char.fieldVchar |>.getD true)

/--
Use `isFieldValueImpl` at run time while leaving the list-based version for proofs.
-/
@[csimp]
theorem isFieldValue_eq_isFieldValueImpl : isFieldValue = isFieldValueImpl := by
  funext s
  simp [isFieldValue, isFieldValueImpl, String.all_bool_eq, String.front?_eq, String.back?_eq]

private theorem utf8EncodeChar_ofUInt8 {x : UInt8} (h : x < 128) :
    String.utf8EncodeChar (Char.ofUInt8 x) = [x] := by
  have hx : x.toNat < 128 := by simpa using UInt8.lt_iff_toNat_lt.mp h
  have hv : (Char.ofUInt8 x).val ≤ 0x7F := by
    simp only [Char.ofUInt8, UInt32.le_iff_toNat_le]; simp; omega
  rw [String.utf8EncodeChar_eq_singleton (by simp [Char.utf8Size, hv])]
  congr 1
  apply UInt8.toNat_inj.mp
  simp [Char.ofUInt8]

private theorem utf8Encode_map_ofUInt8 (l : List UInt8) (h : ∀ x ∈ l, x < 128) :
    (l.map Char.ofUInt8).utf8Encode = l.toByteArray := by
  rw [List.utf8Encode_eq_toByteArray, List.flatMap_map]
  congr 1
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, utf8EncodeChar_ofUInt8 (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]
    rfl

private theorem ascii_mem {b : ByteArray} (h : b.data.all (· < 128)) :
    ∀ x ∈ b.data.toList, x < 128 :=
  fun x hx => by simpa using Array.all_eq_true_iff_forall_mem.mp h x (by simpa using hx)

private theorem toByteArray_data (b : ByteArray) : b.data.toList.toByteArray = b := by
  apply ByteArray.ext; simp

/--
The string of bytes that are all ASCII, without validating them again: each byte is the character
with its code (`toList_ofAsciiBytes`).
-/
def ofAsciiBytes (b : ByteArray) (h : b.data.all (· < 128)) : String :=
  String.ofByteArray b ⟨b.data.toList.map Char.ofUInt8, by
    rw [utf8Encode_map_ofUInt8 _ (ascii_mem h), toByteArray_data]⟩

/--
The characters of `ofAsciiBytes b h` are the bytes of `b`.
-/
theorem toList_ofAsciiBytes (b : ByteArray) (h : b.data.all (· < 128)) :
    (ofAsciiBytes b h).toList = b.data.toList.map Char.ofUInt8 := by
  have : ofAsciiBytes b h = String.ofList (b.data.toList.map Char.ofUInt8) := by
    rw [← String.toByteArray_inj, String.toByteArray_ofList,
      utf8Encode_map_ofUInt8 _ (ascii_mem h), toByteArray_data]
    rfl
  rw [this, String.toList_ofList]

end Std.Http.Internal
