/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Basic
import Lean.Parser.Extra

namespace Lean.Parser

builtin_initialize
  registerBuiltinParserAttribute `builtinPrioParser `prio LeadingIdentBehavior.both
  registerBuiltinDynamicParserAttribute `prioParser `prio

builtin_initialize
  registerBuiltinParserAttribute `builtinAttrParser `attr LeadingIdentBehavior.symbol
  registerBuiltinDynamicParserAttribute `attrParser `attr

@[inline] def priorityParser (rbp : Nat := 0) : Parser :=
  categoryParser `prio rbp

@[inline] def attrParser (rbp : Nat := 0) : Parser :=
  categoryParser `attr rbp

attribute [runBuiltinParserAttributeHooks]
  priorityParser attrParser

namespace Priority
@[builtinPrioParser] def numPrio  := checkPrec maxPrec >> numLit
attribute [runBuiltinParserAttributeHooks] numPrio
end Priority

namespace Attr

@[builtinAttrParser] def simple     := leading_parser ident >> optional (priorityParser <|> ident)
/- Remark, We can't use `simple` for `class`, `instance`, `export`, and `macro` because they are  keywords. -/
@[builtinAttrParser] def «macro»    := leading_parser "macro " >> ident
@[builtinAttrParser] def «export»   := leading_parser "export " >> ident

/- We don't use `simple` for recursor because the argument is not a priority-/
@[builtinAttrParser] def recursor        := leading_parser nonReservedSymbol "recursor " >> numLit
@[builtinAttrParser] def «class»         := leading_parser "class"
@[builtinAttrParser] def «instance»      := leading_parser "instance" >> optional priorityParser
@[builtinAttrParser] def defaultInstance := leading_parser nonReservedSymbol "defaultInstance " >> optional priorityParser

def externEntry := leading_parser optional ident >> optional (nonReservedSymbol "inline ") >> strLit
@[builtinAttrParser] def extern     := leading_parser nonReservedSymbol "extern " >> optional numLit >> many externEntry

end Attr

end Lean.Parser
