/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data.URI.Basic
public import Std.Internal.Http.Data.URI.Parser

public section

/-!
# URI

This module defines the `URI` and `RequestTarget` types that represent and manipulate components of
URIs as defined by RFC 3986. It provides parsing, rendering, and normalization utilities for working
with URIs and request targets in HTTP messages.
-/

namespace Std.Http.RequestTarget

set_option linter.all true

/--
Attempts to parse a `RequestTarget` from the given string.
-/
@[inline]
def parse? (string : String) : Option RequestTarget :=
  (URI.Parser.parseRequestTarget <* Std.Internal.Parsec.eof).run string.toUTF8 |>.toOption

/--
Parses a `RequestTarget` from the given string. Panics if parsing fails. Use `parse?`
if you need a safe option-returning version.
-/
@[inline]
def parse! (string : String) : RequestTarget :=
  match parse? string with
  | some res => res
  | none => panic! "invalid request target"

/--
Creates an origin-form request target from a path string.
The path should start with '/' (e.g., "/api/users" or "/search?q=test").
Panics if the string is not a valid origin-form request target.
-/
@[inline]
def originForm! (path : String) : RequestTarget :=
  match parse? path with
  | some (.originForm p q) => .originForm p q
  | _ => panic! s!"invalid origin-form request target: {path}"

end RequestTarget

namespace URI

/--
Attempts to parse a `URI` from the given string.
-/
@[inline]
def parse? (string : String) : Option URI :=
  (Parser.parseURI <* Std.Internal.Parsec.eof).run string.toUTF8 |>.toOption

/--
Parses a `URI` from the given string. Panics if parsing fails. Use `parse?` if you need a safe
option-returning version.
-/
@[inline]
def parse! (string : String) : URI :=
  match parse? string with
  | some res => res
  | none => panic! "invalid URI"

end URI
