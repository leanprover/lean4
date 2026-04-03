/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ToString
public import Std.Internal.Http.Internal
import Init.Data.String.Search
import Init.Data.String.Iter

public section

/-!
# Header Names

This module defines the `Name` type, which represents validated HTTP header names that conform to
HTTP standards.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#section-5
-/

namespace Std.Http.Header

set_option linter.all true

open Internal Char

/--
Proposition asserting that a string is a valid HTTP header name: all characters are valid token
characters and the string is non-empty.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-names
-/
abbrev IsValidHeaderName (s : String) : Prop :=
  isToken s

/--
A validated HTTP header name that ensures all characters conform to HTTP standards. Header names are
case-insensitive according to HTTP specifications.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-field-names
-/
@[ext]
structure Name where
  /--
  The lowercased normalized header name string.
  -/
  value : String

  /--
  The proof that it's a valid header name.
  -/
  isValidHeaderValue : IsValidHeaderName value := by decide

  /--
  The proof that we stored the header name in stored as a lower case string.
  -/
  isLowerCase : IsLowerCase value := by decide
deriving Repr, DecidableEq

namespace Name

instance : BEq Name where
  beq a b := a.value = b.value

instance : Hashable Name where
  hash x := Hashable.hash x.value

theorem Name.beq_eq {x y : Name} : (x == y) = (x.value == y.value) :=
  rfl

instance : LawfulBEq Name where
  rfl {x} := by simp [Name.beq_eq]
  eq_of_beq {x y} := by grind [Name.beq_eq, Name.ext]

instance : LawfulHashable Name := inferInstance

instance : Inhabited Name where
  default := ⟨"_", by decide, by decide⟩

/--
Attempts to create a `Name` from a `String`, returning `none` if the string contains invalid
characters for HTTP header names or is empty.
-/
def ofString? (s : String) : Option Name :=
  let val := s.trimAscii.toString.toLower
  if h : IsValidHeaderName val ∧ IsLowerCase val then
    some ⟨val, h.left, h.right⟩
  else
    none

/--
Creates a `Name` from a string, panicking with an error message if the string contains invalid
characters for HTTP header names or is empty.
-/
def ofString! (s : String) : Name :=
  match ofString? s with
  | some res => res
  | none => panic! s!"invalid header name: {s.quote}"

/--
Converts the header name to title case (e.g., "Content-Type").

Note: some well-known headers have unconventional casing (e.g., "WWW-Authenticate"),
but since HTTP header names are case-insensitive, this always uses simple capitalization.
-/
@[inline]
def toCanonical (name : Name) : String :=
  let it := name.value.split '-'
    |>.map (·.copy.capitalize)

  it.intercalateString "-"

/--
Performs a case-insensitive comparison between a `Name` and a `String`. Returns `true` if they match.
-/
@[expose]
def is (name : Name) (s : String) : Bool :=
  name.value == s.toLower

instance : ToString Name where
  toString name := name.toCanonical

/--
Standard Content-Type header name
-/
def contentType : Header.Name := .mk "content-type"

/--
Standard Content-Length header name
-/
def contentLength : Header.Name := .mk "content-length"

/--
Standard Host header name
-/
def host : Header.Name := .mk "host"

/--
Standard Authorization header name
-/
def authorization : Header.Name := .mk "authorization"

/--
Standard User-Agent header name
-/
def userAgent : Header.Name := .mk "user-agent"

/--
Standard Accept header name
-/
def accept : Header.Name := .mk "accept"

/--
Standard Connection header name
-/
def connection : Header.Name := .mk "connection"

/--
Standard Transfer-Encoding header name
-/
def transferEncoding : Header.Name := .mk "transfer-encoding"

/--
Standard Server header name
-/
def server : Header.Name := .mk "server"

/--
Standard Date header name
-/
def date : Header.Name := .mk "date"

/--
Standard Expect header name
-/
def expect : Header.Name := .mk "expect"

end Std.Http.Header.Name
