/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Extension
-- necessary for auto-generation
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter

namespace Lean
namespace Parser

-- synthesize pretty printers for parsers declared prior to `Lean.PrettyPrinter`
-- (because `Parser.Extension` depends on them)
attribute [runBuiltinParserAttributeHooks]
  leadingNode termParser commandParser antiquotNestedExpr antiquotExpr mkAntiquot nodeWithAntiquot
  ident numLit scientificLit charLit strLit nameLit

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

section
open PrettyPrinter

@[combinatorFormatter Lean.Parser.ppHardSpace] def ppHardSpace.formatter : Formatter := Formatter.push " "
@[combinatorFormatter Lean.Parser.ppSpace] def ppSpace.formatter : Formatter := Formatter.pushLine
@[combinatorFormatter Lean.Parser.ppLine] def ppLine.formatter : Formatter := Formatter.push "\n"
@[combinatorFormatter Lean.Parser.ppGroup] def ppGroup.formatter (p : Formatter) : Formatter := Formatter.group $ Formatter.indent p
@[combinatorFormatter Lean.Parser.ppIndent] def ppIndent.formatter (p : Formatter) : Formatter := Formatter.indent p
@[combinatorFormatter Lean.Parser.ppDedent] def ppDedent.formatter (p : Formatter) : Formatter := do
  let opts ← getOptions
  Formatter.indent p (some ((0:Int) - Format.getIndent opts))
end

namespace Parser

-- now synthesize parenthesizers
attribute [runBuiltinParserAttributeHooks]
  ppHardSpace ppSpace ppLine ppGroup ppIndent ppDedent

macro "registerParserAlias!" aliasName:strLit declName:ident : term =>
  `(do Parser.registerAlias $aliasName $declName
       PrettyPrinter.Formatter.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `formatter))
       PrettyPrinter.Parenthesizer.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `parenthesizer)))

builtin_initialize
  registerParserAlias! "group" group
  registerParserAlias! "ppHardSpace" ppHardSpace
  registerParserAlias! "ppSpace" ppSpace
  registerParserAlias! "ppLine" ppLine
  registerParserAlias! "ppGroup" ppGroup
  registerParserAlias! "ppIndent" ppIndent
  registerParserAlias! "ppDedent" ppDedent

end Parser
end Lean
