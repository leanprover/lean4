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
# Header Names

This module defines the `Name` type, which represents validated HTTP header names that conform to
HTTP standards.
-/

namespace Std.Http.Header

set_option linter.all true

open Internal

/--
Checks if a character is valid for use in an HTTP header name.
-/
@[expose]
def isValidHeaderNameChar (c : Char) : Bool :=
  c.toNat < 128 && Nat.testBit 0x57ffffffc7fffffe03ff6cfa00000000 c.toNat

/--
Proposition that asserts all characters in a string are valid and that it is non-empty for HTTP header names.
-/
abbrev IsValidHeaderName (s : String) : Prop :=
  s.toList.all isValidHeaderNameChar ∧ ¬s.isEmpty

/--
A validated HTTP header name that ensures all characters conform to HTTP standards. Header names are
case-insensitive according to HTTP specifications.
-/
structure Name where
  /--
  The lowercased normalized header name string.
  -/
  value : String

  /--
  The proof that it's a valid header name
  -/
  validHeaderName : IsValidHeaderName value := by decide

  /--
  The proof that we stored the header name in normal form
  -/
  normalForm : IsLowerCase value := by decide
deriving Repr, DecidableEq, BEq

namespace Name

instance : Hashable Name where
  hash x := Hashable.hash x.value

instance : Inhabited Name where
  default := ⟨"_", by decide, by decide⟩

/--
Attempts to create a `Name` from a `String`, returning `none` if the string contains invalid
characters for HTTP header names or is empty.
-/
@[expose]
def ofString? (s : String) : Option Name :=
  let val := s.toLower
  if h : IsValidHeaderName val ∧ IsLowerCase val then
    some ⟨val, h.left, h.right⟩
  else
    none

/--
Creates a `Name` from a string, panicking with an error message if the
string contains invalid characters for HTTP header names or is empty.
-/
@[expose]
def ofString! (s : String) : Name :=
  let val := s.toLower
  if h : IsValidHeaderName val ∧ IsLowerCase val then
    ⟨val, h.left, h.right⟩
  else
    panic! s!"invalid header name: {s.quote}"

/--
Converts the header name to title case (e.g., "Content-Type").

Note: some well-known headers have unconventional casing (e.g., "WWW-Authenticate"),
but since HTTP header names are case-insensitive, this always uses simple capitalization.
-/
@[inline]
def toCanonical (name : Name) : String :=
  let it := name.value.splitOn "-"
    |>.map (·.capitalize)

  String.intercalate "-" it

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
