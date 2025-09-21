/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Encode
public import Std.Internal.Http.Data.URI.Basic
public import Std.Internal.Http.Data.URI.Parser

public section

namespace Std
namespace Http
namespace RequestTarget

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
