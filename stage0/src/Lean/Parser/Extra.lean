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
  leadingNode termParser commandParser mkAntiquot nodeWithAntiquot sepBy sepBy1
  unicodeSymbol nonReservedSymbol

@[runBuiltinParserAttributeHooks] def optional (p : Parser) : Parser :=
  optionalNoAntiquot (withAntiquotSpliceAndSuffix `optional p (symbol "?"))

@[runBuiltinParserAttributeHooks] def many (p : Parser) : Parser :=
  manyNoAntiquot (withAntiquotSpliceAndSuffix `many p (symbol "*"))

@[runBuiltinParserAttributeHooks] def many1 (p : Parser) : Parser :=
  many1NoAntiquot (withAntiquotSpliceAndSuffix `many p (symbol "*"))

@[runBuiltinParserAttributeHooks] def ident : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) identNoAntiquot

-- `ident` and `rawIdent` produce the same syntax tree, so we reuse the antiquotation kind name
@[runBuiltinParserAttributeHooks] def rawIdent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) rawIdentNoAntiquot

@[runBuiltinParserAttributeHooks] def numLit : Parser :=
  withAntiquot (mkAntiquot "num" numLitKind) numLitNoAntiquot

@[runBuiltinParserAttributeHooks] def scientificLit : Parser :=
  withAntiquot (mkAntiquot "scientific" scientificLitKind) scientificLitNoAntiquot

@[runBuiltinParserAttributeHooks] def strLit : Parser :=
  withAntiquot (mkAntiquot "str" strLitKind) strLitNoAntiquot

@[runBuiltinParserAttributeHooks] def charLit : Parser :=
  withAntiquot (mkAntiquot "char" charLitKind) charLitNoAntiquot

@[runBuiltinParserAttributeHooks] def nameLit : Parser :=
  withAntiquot (mkAntiquot "name" nameLitKind) nameLitNoAntiquot

@[runBuiltinParserAttributeHooks, inline] def group (p : Parser) : Parser :=
  node groupKind p

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
/-- No-op parser combinator that advises the pretty printer to emit a `Format.fill` node. -/
@[inline] def ppRealFill : Parser → Parser := id
/-- No-op parser combinator that advises the pretty printer to emit a `Format.group` node. -/
@[inline] def ppRealGroup : Parser → Parser := id
/-- No-op parser combinator that advises the pretty printer to indent the given syntax without grouping it. -/
@[inline] def ppIndent : Parser → Parser := id
/--
  No-op parser combinator that advises the pretty printer to group and indent the given syntax.
  By default, only syntax categories are grouped. -/
@[inline] def ppGroup (p : Parser) : Parser := ppRealFill (ppIndent p)
/--
  No-op parser combinator that advises the pretty printer to dedent the given syntax.
  Dedenting can in particular be used to counteract automatic indentation. -/
@[inline] def ppDedent : Parser → Parser := id

/--
  No-op parser combinator that allows the pretty printer to omit the group and
  indent operation in the enclosing category parser.
  ```
  syntax ppAllowUngrouped "by " tacticSeq : term
  -- allows a `by` after `:=` without linebreak in between:
  theorem foo : True := by
    trivial
  ```
-/
@[inline] def ppAllowUngrouped : Parser := skip

/--
  No-op parser combinator that advises the pretty printer to dedent the given syntax,
  if it was grouped by the category parser.
  Dedenting can in particular be used to counteract automatic indentation. -/
@[inline] def ppDedentIfGrouped : Parser → Parser := id

/--
  No-op parser combinator that prints a line break.
  The line break is soft if the combinator is followed
  by an ungrouped parser (see ppAllowUngrouped), otherwise hard. -/
@[inline] def ppHardLineUnlessUngrouped : Parser := skip

end Parser

section
open PrettyPrinter

@[combinatorFormatter Lean.Parser.ppHardSpace] def ppHardSpace.formatter : Formatter := Formatter.pushWhitespace " "
@[combinatorFormatter Lean.Parser.ppSpace] def ppSpace.formatter : Formatter := Formatter.pushLine
@[combinatorFormatter Lean.Parser.ppLine] def ppLine.formatter : Formatter := Formatter.pushWhitespace "\n"
@[combinatorFormatter Lean.Parser.ppRealFill] def ppRealFill.formatter (p : Formatter) : Formatter := Formatter.fill p
@[combinatorFormatter Lean.Parser.ppRealGroup] def ppRealGroup.formatter (p : Formatter) : Formatter := Formatter.group p
@[combinatorFormatter Lean.Parser.ppIndent] def ppIndent.formatter (p : Formatter) : Formatter := Formatter.indent p
@[combinatorFormatter Lean.Parser.ppDedent] def ppDedent.formatter (p : Formatter) : Formatter := do
  let opts ← getOptions
  Formatter.indent p (some ((0:Int) - Std.Format.getIndent opts))

@[combinatorFormatter Lean.Parser.ppAllowUngrouped] def ppAllowUngrouped.formatter : Formatter := do
  modify ({ · with mustBeGrouped := false })
@[combinatorFormatter Lean.Parser.ppDedentIfGrouped] def ppDedentIfGrouped.formatter (p : Formatter) : Formatter := do
  Formatter.concat p
  let indent := Std.Format.getIndent (← getOptions)
  unless (← get).isUngrouped do
    modify fun st => { st with stack := st.stack.modify (st.stack.size - 1) (·.nest (0 - indent)) }
@[combinatorFormatter Lean.Parser.ppHardLineUnlessUngrouped] def ppHardLineUnlessUngrouped.formatter : Formatter := do
  if (← get).isUngrouped then
    Formatter.pushLine
  else
    ppLine.formatter

end

namespace Parser

-- now synthesize parenthesizers
attribute [runBuiltinParserAttributeHooks]
  ppHardSpace ppSpace ppLine ppGroup ppRealGroup ppRealFill ppIndent ppDedent
  ppAllowUngrouped ppDedentIfGrouped ppHardLineUnlessUngrouped

macro "register_parser_alias" aliasName?:optional(strLit) declName:ident : term =>
  let aliasName := aliasName?.getD (Syntax.mkStrLit declName.getId.toString)
  `(do Parser.registerAlias $aliasName $declName
       PrettyPrinter.Formatter.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `formatter))
       PrettyPrinter.Parenthesizer.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `parenthesizer)))

builtin_initialize
  register_parser_alias group
  register_parser_alias ppHardSpace
  register_parser_alias ppSpace
  register_parser_alias ppLine
  register_parser_alias ppGroup
  register_parser_alias ppRealGroup
  register_parser_alias ppRealFill
  register_parser_alias ppIndent
  register_parser_alias ppDedent
  register_parser_alias ppAllowUngrouped
  register_parser_alias ppDedentIfGrouped
  register_parser_alias ppHardLineUnlessUngrouped

end Parser

end Lean
