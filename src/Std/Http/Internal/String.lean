/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
public import Init.Data.String.TakeDrop
public import Std.Http.Internal.Char

public section


/-!
# Internal String Helpers

Shared string utilities for HTTP: token validation and quoted-string encoding/decoding for header
parameter values and chunk extensions.
-/

namespace Std.Http.Internal

open Char

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
def isToken (s : String) : Bool :=
  let s := s.toList
  ¬s.isEmpty ∧ s.all Char.tchar

end Std.Http.Internal
