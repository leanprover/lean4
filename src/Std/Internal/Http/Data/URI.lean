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
Attempt to parse a `RequestTarget` from the given string.
-/
@[inline]
def parse? (string : String) : Option RequestTarget :=
  Parser.parseRequestTarget.run string.toUTF8 |>.toOption

/--
Parse a `RequestTarget` from the given string. Panics if parsing fails. Use `parse?`
if you need a safe option-returning version.
-/
@[inline]
def parse! (string : String) : RequestTarget :=
  parse? string |>.get!
