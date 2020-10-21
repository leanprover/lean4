#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

import Lean.Parser.Basic

-- necessary for auto-generation
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter

namespace Lean
namespace Parser

-- synthesize pretty printers for parsers declared prior to `Lean.PrettyPrinter`
-- (because `Parser.Extension` depends on them)
attribute [runBuiltinParserAttributeHooks]
  leadingNode termParser commandParser antiquotNestedExpr antiquotExpr mkAntiquot nodeWithAntiquot
  ident numLit charLit strLit nameLit

@[runBuiltinParserAttributeHooks, inline] def group (p : Parser) : Parser :=
  node nullKind p

@[runBuiltinParserAttributeHooks, inline] def many1Indent (p : Parser) : Parser :=
  withPosition $ many1 (checkColGe "irrelevant" >> p)

@[runBuiltinParserAttributeHooks, inline] def manyIndent (p : Parser) : Parser :=
  withPosition $ many (checkColGe "irrelevant" >> p)

@[runBuiltinParserAttributeHooks] abbrev notSymbol (s : String) : Parser :=
  notFollowedBy (symbol s) s

/-- No-op parser that advises the pretty printer to emit a non-breaking space. -/
@[inline] def ppHardSpace : Parser := skip
/-- No-op parser that advises the pretty printer to emit a space/soft line break. -/
@[inline] def ppSpace : Parser := skip
/-- No-op parser that advises the pretty printer to emit a hard line break. -/
@[inline] def ppLine : Parser := skip
/--
  No-op parser combinator that advises the pretty printer to group and indent the given syntax.
  By default, only syntax categories are grouped. -/
@[inline] def ppGroup : Parser → Parser := id
/-- No-op parser combinator that advises the pretty printer to indent the given syntax without grouping it. -/
@[inline] def ppIndent : Parser → Parser := id
/--
  No-op parser combinator that advises the pretty printer to dedent the given syntax.
  Dedenting can in particular be used to counteract automatic indentation. -/
@[inline] def ppDedent : Parser → Parser := id

end Parser

namespace PrettyPrinter
namespace Formatter

@[combinatorFormatter Lean.Parser.ppHardSpace] def ppHardSpace.formatter : Formatter := push " "
@[combinatorFormatter Lean.Parser.ppSpace] def ppSpace.formatter : Formatter := pushLine
@[combinatorFormatter Lean.Parser.ppLine] def ppLine.formatter : Formatter := push "\n"
@[combinatorFormatter Lean.Parser.ppGroup] def ppGroup.formatter (p : Formatter) : Formatter := group $ indent p
@[combinatorFormatter Lean.Parser.ppIndent] def ppIndent.formatter (p : Formatter) : Formatter := indent p
@[combinatorFormatter Lean.Parser.ppDedent] def ppDedent.formatter (p : Formatter) : Formatter := do
  let opts ← getOptions
  indent p (some (0 - Format.getIndent opts))

end Formatter
end PrettyPrinter

namespace Parser

-- now synthesize parenthesizers
attribute [runBuiltinParserAttributeHooks]
  ppHardSpace ppSpace ppLine ppGroup ppIndent ppDedent

end Parser
end Lean
