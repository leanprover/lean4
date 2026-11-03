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
Quotes `s` as an HTTP `quoted-string`: `DQUOTE *( qdtext / quoted-pair ) DQUOTE`.

Requires a proof that every character passes `quotedStringChar`. This function always adds quotes;
use `quoteHttpString` to preserve valid tokens.
-/
@[expose]
def quoteHttpStringCore (s : String) (_h : s.toList.all quotedStringChar) : String :=
  let quoteChar (out : String) (c : Char) : String :=
    (if c == '"' || c == '\\' then out.push '\\' else out).push c
  (s.foldl quoteChar "\"").push '"'

/--
Quotes `s` as an HTTP `quoted-string` if necessary, otherwise returns `s`.

If every character is a `tchar` and the string is non-empty, the string is returned as-is (it is
already a valid token). Otherwise the string is wrapped in double quotes, escaping `"` and `\`
as `quoted-pair`.

Requires a proof that every character passes `quotedStringChar`.
-/
@[expose]
def quoteHttpString (s : String) (h : s.toList.all quotedStringChar) : String :=
  if !s.isEmpty && s.all tchar then
    s
  else
    quoteHttpStringCore s h

/--
Attempts to quote `s` as an HTTP `quoted-string`.

Returns `some` with the quoted result when every character passes `quotedStringChar`, or `none`
when any character cannot be represented by the grammar.
-/
def quoteHttpString? (s : String) : Option String :=
  if h : s.all quotedStringChar then
    some <| quoteHttpString s (by simpa [String.all_bool_eq] using h)
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
Returns `true` if `s` neither starts nor ends with ASCII whitespace, so that `s.trimAscii` is all of
`s`.
-/
def isAsciiTrimmed (s : String) : Bool :=
  if h : 0 < s.utf8ByteSize then
    let ws (b : UInt8) := b == ' '.toUInt8 || b == '\t'.toUInt8 || b == '\r'.toUInt8 || b == '\n'.toUInt8
    !ws (s.getUTF8Byte ⟨0⟩ h) &&
      !ws (s.getUTF8Byte ⟨s.utf8ByteSize - 1⟩ (by
        show s.utf8ByteSize - 1 < s.utf8ByteSize
        omega))
  else
    true

/--
Checks whether a string is a valid non-empty HTTP token.
-/
@[expose]
def isToken (s : String) : Bool :=
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

end Std.Http.Internal
