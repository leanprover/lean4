/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
public import Init.Data.String
public import Std.Internal.Http.Internal.Char

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
Core character quoting used by `String.quote`.

In string context (`inString := true`), this emits:
- `qdtext` characters directly
- `"` and `\\` as `quoted-pair`
and panics for characters outside the grammar.
-/
def quoteCore (c : Char) (inString : Bool := false) : String :=
  if inString then
    if qdtext c then
      .singleton c
    else if c = '\\' || c = '\"' then
      .append "\\" (.singleton c)
    else
      panic! "invalid HTTP quoted-string content"
  else
    if quotedPairChar c then
      .singleton c
    else
      panic! "invalid HTTP quoted-pair content"

/--
Attempts to quote `s` as an HTTP `quoted-string`:
`DQUOTE *( qdtext / quoted-pair ) DQUOTE`.

Returns `none` when any character in `s` cannot be represented by the grammar.
-/
@[expose]
def quoteHttpString? (s : String) : Option String :=
  if s.all tchar ∧ ¬s.isEmpty then
    some s
  else if s.all quotedStringChar then
    some (.append
      (.foldl (fun acc c =>
        .append acc (quoteCore c (inString := true))) "\"" s)
      "\"")
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
