/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Extra

namespace Lean
namespace Parser

builtin_initialize
  registerBuiltinParserAttribute `builtin_level_parser ``Category.level

@[inline] def levelParser (rbp : Nat := 0) : Parser :=
  categoryParser `level rbp

namespace Level

@[builtin_level_parser] def paren  := leading_parser
  "(" >> withoutPosition levelParser >> ")"
@[builtin_level_parser] def max    := leading_parser
  nonReservedSymbol "max" true  >> many1 (ppSpace >> levelParser maxPrec)
@[builtin_level_parser] def imax   := leading_parser
  nonReservedSymbol "imax" true >> many1 (ppSpace >> levelParser maxPrec)
@[builtin_level_parser] def hole   := leading_parser
  "_"
@[builtin_level_parser] def num    :=
  checkPrec maxPrec >> numLit
@[builtin_level_parser] def ident  :=
  checkPrec maxPrec >> Parser.ident
@[builtin_level_parser] def addLit := trailing_parser:65
  " + " >> numLit

end Level

end Parser
end Lean
