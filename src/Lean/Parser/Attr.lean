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
  registerBuiltinParserAttribute `builtinAttrParamParser `attrParam
  registerBuiltinDynamicParserAttribute `attrParamParser `attrParam

builtin_initialize
  registerBuiltinParserAttribute `builtinAttrParser `attr LeadingIdentBehavior.symbol
  registerBuiltinDynamicParserAttribute `attrParser `attr

@[inline] def priorityParser (rbp : Nat := 0) : Parser :=
  categoryParser `prio rbp

@[inline] def attrParamParser (rbp : Nat := 0) : Parser :=
  categoryParser `attrParam rbp

@[inline] def attrParser (rbp : Nat := 0) : Parser :=
  categoryParser `attr rbp

attribute [runBuiltinParserAttributeHooks]
  priorityParser attrParamParser attrParser

namespace Priority
@[builtinPrioParser] def numPrio  := checkPrec maxPrec >> numLit
@[builtinPrioParser] def highPrio := parser!:maxPrec nonReservedSymbol "high"

attribute [runBuiltinParserAttributeHooks]
  numPrio highPrio

end Priority

namespace AttrParam
@[builtinAttrParamParser] def ident := checkPrec maxPrec >> Parser.ident
@[builtinAttrParamParser] def str   := checkPrec maxPrec >> strLit
@[builtinAttrParamParser] def num   := checkPrec maxPrec >> numLit
@[builtinAttrParamParser] def prio  := parser!:maxPrec "priority: " >> priorityParser maxPrec

attribute [runBuiltinParserAttributeHooks]
  ident str num prio

end AttrParam

namespace Attr

@[builtinAttrParser] def simple     := parser! ident >> optional ident >> optional priorityParser
/- We can't use `simple` for `class`, `instance`, and `macro` because they are  keywords. -/
@[builtinAttrParser] def «class»    := parser! "class"
@[builtinAttrParser] def «instance» := parser! "instance" >> optional priorityParser
@[builtinAttrParser] def «macro»    := parser! "macro " >> ident

def externEntry := parser! optional (nonReservedSymbol "inline ") >> optional ident >> strLit
@[builtinAttrParser] def extern     := parser! nonReservedSymbol "extern " >> optional numLit >> many externEntry

end Attr

end Lean.Parser
