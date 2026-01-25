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
# Header Names and Values

This module defines the `Name` and `Value` types, which represent validated HTTP header names and
values that conform to HTTP standards.
-/

namespace Std.Http.Header

set_option linter.all true

open Internal

/--
Checks if a character is valid for use in an HTTP header name.
-/
def isValidHeaderNameChar (c : Char) : Bool :=
  c ≥'!' &&  c ≤ '~' && c != '"' && c != '(' && c != ')' && c != ',' && c != ';' &&
  c != '[' && c != ']' && c != '{' && c != '}'

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
  validHeaderName : IsValidHeaderName value

  /--
  The proof that we stored the header name in normal form
  -/
  normalForm : IsLowerCase value
deriving Repr, DecidableEq, BEq

namespace Name

instance : Hashable Name where
  hash x := Hashable.hash x.value

instance : Inhabited Name where
  default := ⟨"_", by decide, by decide⟩

/--
Creates a new `Name` from a string with an optional proof of validity. If no proof is provided, it
attempts to prove validity automatically.
-/
@[expose]
def new (s : String) (h : IsValidHeaderName s := by decide) (h₁ : IsLowerCase s := by decide) : Name :=
  ⟨s, h, h₁⟩

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
Converts the header name to canonical HTTP title case (e.g., "Content-Type").
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
def contentType : Header.Name := .new "content-type"

/--
Standard Content-Length header name
-/
def contentLength : Header.Name := .new "content-length"

/--
Standard Host header name
-/
def host : Header.Name := .new "host"

/--
Standard Authorization header name
-/
def authorization : Header.Name := .new "authorization"

/--
Standard User-Agent header name
-/
def userAgent : Header.Name := .new "user-agent"

/--
Standard Accept header name
-/
def accept : Header.Name := .new "accept"

/--
Standard Connection header name
-/
def connection : Header.Name := .new "connection"

/--
Standard Transfer-Encoding header name
-/
def transferEncoding : Header.Name := .new "transfer-encoding"

/--
Standard Server header name
-/
def server : Header.Name := .new "server"

end Std.Http.Header.Name
