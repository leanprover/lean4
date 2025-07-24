/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Parser.Basic
public import Lean.Parser.Extra

public section

namespace Lean.Parser

builtin_initialize
  registerBuiltinParserAttribute `builtin_prio_parser ``Category.prio .both
  registerBuiltinDynamicParserAttribute `prio_parser `prio

builtin_initialize
  registerBuiltinParserAttribute `builtin_attr_parser ``Category.attr .symbol
  registerBuiltinDynamicParserAttribute `attr_parser `attr

@[inline] def priorityParser (rbp : Nat := 0) : Parser :=
  categoryParser `prio rbp

@[inline] def attrParser (rbp : Nat := 0) : Parser :=
  categoryParser `attr rbp

attribute [run_builtin_parser_attribute_hooks]
  priorityParser attrParser

namespace Priority
@[builtin_prio_parser] def numPrio  := checkPrec maxPrec >> numLit
attribute [run_builtin_parser_attribute_hooks] numPrio
end Priority

namespace Attr

@[builtin_attr_parser] def simple     := leading_parser ident >> optional (ppSpace >> (priorityParser <|> ident))
/- Remark, We can't use `simple` for `class`, `instance`, `export`, and `macro` because they are keywords. -/
@[builtin_attr_parser] def «macro»    := leading_parser "macro " >> ident
@[builtin_attr_parser] def «export»   := leading_parser "export " >> ident

/- We don't use `simple` for recursor because the argument is not a priority -/
@[builtin_attr_parser] def recursor         := leading_parser nonReservedSymbol "recursor " >> numLit
@[builtin_attr_parser] def «class»          := leading_parser "class"
@[builtin_attr_parser] def «instance»       := leading_parser "instance" >> optional (ppSpace >> priorityParser)
@[builtin_attr_parser] def default_instance := leading_parser nonReservedSymbol "default_instance" >> optional (ppSpace >> priorityParser)
@[builtin_attr_parser] def «specialize»     := leading_parser (nonReservedSymbol "specialize") >> many (ppSpace >> (ident <|> numLit))

def externEntry := leading_parser
  optional (ident >> ppSpace) >> optional (nonReservedSymbol "inline ") >> strLit
@[builtin_attr_parser] def extern     := leading_parser
  nonReservedSymbol "extern" >> optional (ppSpace >> numLit) >> many (ppSpace >> externEntry)

/--
Declare this tactic to be an alias or alternative form of an existing tactic.

This has the following effects:
 * The alias relationship is saved
 * The docstring is taken from the original tactic, if present
-/
@[builtin_attr_parser] def «tactic_alt» := leading_parser
  "tactic_alt" >> ppSpace >> ident

/--
Add one or more tags to a tactic.

Tags should be applied to the canonical names for tactics.
-/
@[builtin_attr_parser] def «tactic_tag» := leading_parser
  "tactic_tag" >> many1 (ppSpace >> ident)

end Attr

end Lean.Parser
