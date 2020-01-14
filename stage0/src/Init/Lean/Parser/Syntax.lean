/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Parser

namespace Lean
namespace Parser

@[init] def regBuiltinSyntaxParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinSyntaxParser `syntax

@[init] def regSyntaxParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `syntaxParser `syntax

@[inline] def syntaxParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `syntax rbp

namespace Syntax


end Syntax
end Parser
end Lean
