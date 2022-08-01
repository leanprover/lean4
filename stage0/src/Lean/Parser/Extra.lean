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

@[inline] def sepByIndent (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  withPosition $ sepBy (checkColGe "irrelevant" >> p) sep (psep <|> checkLinebreakBefore >> pushNone) allowTrailingSep

@[inline] def sepBy1Indent (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  withPosition $ sepBy1 (checkColGe "irrelevant" >> p) sep (psep <|> checkLinebreakBefore >> pushNone) allowTrailingSep

open PrettyPrinter Syntax.MonadTraverser Formatter in
@[combinatorFormatter Lean.Parser.sepByIndent]
def sepByIndent.formatter (p : Formatter) (_sep : String) (pSep : Formatter) : Formatter := do
  let stx ← getCur
  let hasNewlineSep := stx.getArgs.mapIdx (fun ⟨i, _⟩ n => i % 2 == 1 && n.matchesNull 0) |>.any id
  visitArgs do
    for i in (List.range stx.getArgs.size).reverse do
      if i % 2 == 0 then p else pSep <|> (pushWhitespace "\n" *> goLeft)
  -- If there is any newline separator, then we need to force a newline at the
  -- start so that `withPosition` will pick up the right column.
  if hasNewlineSep then
    pushWhitespace "\n"
    -- HACK: allow formatter to put initial brace on previous line in structure instances
    modify ({ · with mustBeGrouped := false })

@[combinatorFormatter Lean.Parser.sepBy1Indent] def sepBy1Indent.formatter := sepByIndent.formatter

attribute [runBuiltinParserAttributeHooks] sepByIndent sepBy1Indent

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

syntax "register_parser_alias" group("(" &"kind" " := " term ")")? (strLit)? ident (colGt term)? : term
macro_rules
  | `(register_parser_alias $[(kind := $kind?)]? $(aliasName?)? $declName $(info?)?) => do
    let [(fullDeclName, [])] ← Macro.resolveGlobalName declName.getId |
      Macro.throwError "expected non-overloaded constant name"
    let aliasName := aliasName?.getD (Syntax.mkStrLit declName.getId.toString)
    `(do Parser.registerAlias $aliasName $declName $(info?.getD (Unhygienic.run `({}))) (kind? := some $(kind?.getD (quote fullDeclName)))
         PrettyPrinter.Formatter.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `formatter))
         PrettyPrinter.Parenthesizer.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `parenthesizer)))

builtin_initialize
  register_parser_alias group { autoGroupArgs := false }
  register_parser_alias ppHardSpace { stackSz? := some 0 }
  register_parser_alias ppSpace { stackSz? := some 0 }
  register_parser_alias ppLine { stackSz? := some 0 }
  register_parser_alias ppGroup { stackSz? := none }
  register_parser_alias ppRealGroup { stackSz? := none }
  register_parser_alias ppRealFill { stackSz? := none }
  register_parser_alias ppIndent { stackSz? := none }
  register_parser_alias ppDedent { stackSz? := none }
  register_parser_alias ppDedentIfGrouped { stackSz? := none }
  register_parser_alias ppAllowUngrouped { stackSz? := some 0 }
  register_parser_alias ppHardLineUnlessUngrouped { stackSz? := some 0 }

end Parser

end Lean
