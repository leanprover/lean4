/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Parser

namespace Lean
namespace Parser

@[init] def regBuiltinLevelParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinLevelParser `level

@[inline] def levelParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `level rbp

namespace Level

@[builtinLevelParser] def paren  := parser! symbol "(" appPrec >> levelParser >> ")"
@[builtinLevelParser] def max    := parser! nonReservedSymbol "max " true  >> many1 (levelParser appPrec)
@[builtinLevelParser] def imax   := parser! "imax" >> many1 (levelParser appPrec)
@[builtinLevelParser] def hole   := parser! "_"
@[builtinLevelParser] def num    := parser! numLit
@[builtinLevelParser] def ident  := parser! ident
@[builtinLevelParser] def addLit := tparser! pushLeading >> symbol "+" (65:Nat) >> numLit

end Level

end Parser
end Lean
