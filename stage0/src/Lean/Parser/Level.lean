/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Parser

namespace Lean
namespace Parser

@[init] def regBuiltinLevelParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinLevelParser `level

@[inline] def levelParser (rbp : Nat := 0) : Parser :=
categoryParser `level rbp

namespace Level

@[builtinLevelParser] def paren  := parser! [appPrec] "(" >> levelParser >> ")"
@[builtinLevelParser] def max    := parser! [appPrec] nonReservedSymbol "max " true  >> many1 (levelParser appPrec)
@[builtinLevelParser] def imax   := parser! [appPrec] nonReservedSymbol "imax " true >> many1 (levelParser appPrec)
@[builtinLevelParser] def hole   := parser! [appPrec] "_"
@[builtinLevelParser] def num    := parser! [appPrec] numLit
@[builtinLevelParser] def ident  := parser! [appPrec] ident
@[builtinLevelParser] def addLit := tparser! [65] "+" >> numLit

end Level

end Parser
end Lean
