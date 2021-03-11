/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Extra

namespace Lean
namespace Parser

builtin_initialize
  registerBuiltinParserAttribute `builtinLevelParser `level

@[inline] def levelParser (rbp : Nat := 0) : Parser :=
  categoryParser `level rbp

namespace Level

@[builtinLevelParser] def paren  := leading_parser "(" >> levelParser >> ")"
@[builtinLevelParser] def max    := leading_parser nonReservedSymbol "max" true  >> many1 (ppSpace >> levelParser maxPrec)
@[builtinLevelParser] def imax   := leading_parser nonReservedSymbol "imax" true >> many1 (ppSpace >> levelParser maxPrec)
@[builtinLevelParser] def hole   := leading_parser "_"
@[builtinLevelParser] def num    := checkPrec maxPrec >> numLit
@[builtinLevelParser] def ident  := checkPrec maxPrec >> Parser.ident
@[builtinLevelParser] def addLit := trailing_parser:65 " + " >> numLit

end Level

end Parser
end Lean
