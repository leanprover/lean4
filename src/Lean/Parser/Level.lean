/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
module

prelude
public import Lean.Parser.Extra

public section

namespace Lean
namespace Parser

builtin_initialize
  registerBuiltinParserAttribute `builtin_level_parser ``Category.level

@[inline] def levelParser (rbp : Nat := 0) : Parser :=
  categoryParser `level rbp

namespace Level

/-- Parenthesized universe level, e.g. `(u)` or `(max u v)`. -/
@[builtin_level_parser] def paren  := leading_parser
  "(" >> withoutPosition levelParser >> ")"
/-- `max`-combinations of universe levels, e.g. `max u v`. -/
@[builtin_level_parser] def max    := leading_parser
  nonReservedSymbol "max" true  >> many1 (ppSpace >> levelParser maxPrec)
/-- `imax`-combinations of universe levels, e.g. `imax u v`. -/
@[builtin_level_parser] def imax   := leading_parser
  nonReservedSymbol "imax" true >> many1 (ppSpace >> levelParser maxPrec)
/-- Hole for a universe level. -/
@[builtin_level_parser] def hole   := leading_parser
  "_"
@[inherit_doc Lean.Parser.numLit, builtin_level_parser] def num    :=
  checkPrec maxPrec >> numLit
@[inherit_doc Lean.Parser.ident, builtin_level_parser] def ident  :=
  checkPrec maxPrec >> Parser.ident
/-- Addition of a numeric literal to a universe level, e.g. `u + 1`. -/
@[builtin_level_parser] def addLit := trailing_parser:65
  " + " >> numLit

end Level

end Parser
end Lean
