/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Extension
-- necessary for auto-generation
import Lean.PrettyPrinter.Parenthesizer
import Lean.PrettyPrinter.Formatter

namespace Lean
namespace Parser

-- synthesize pretty printers for parsers declared prior to `Lean.PrettyPrinter`
-- (because `Parser.Extension` depends on them)
attribute [run_builtin_parser_attribute_hooks]
  leadingNode termParser commandParser mkAntiquot nodeWithAntiquot sepBy sepBy1
  unicodeSymbol nonReservedSymbol
  withCache withResetCache withPosition withPositionAfterLinebreak withoutPosition withForbidden withoutForbidden setExpected
  incQuotDepth decQuotDepth suppressInsideQuot evalInsideQuot
  withOpen withOpenDecl
  dbgTraceState

/-- The parser `optional(p)`, or `(p)?`, parses `p` if it succeeds,
otherwise it succeeds with no value.

Note that because `?` is a legal identifier character, one must write `(p)?` or `p ?` for
it to parse correctly. `ident?` will not work; one must write `(ident)?` instead.

This parser has arity 1: it produces a `nullKind` node containing either zero arguments
(for the `none` case) or the list of arguments produced by `p`.
(In particular, if `p` has arity 0 then the two cases are not differentiated!) -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def optional (p : Parser) : Parser :=
  optionalNoAntiquot (withAntiquotSpliceAndSuffix `optional p (symbol "?"))

/-- The parser `many(p)`, or `p*`, repeats `p` until it fails, and returns the list of results.

The argument `p` is "auto-grouped", meaning that if the arity is greater than 1 it will be
automatically replaced by `group(p)` to ensure that it produces exactly 1 value.

This parser has arity 1: it produces a `nullKind` node containing one argument for each
invocation of `p` (or `group(p)`). -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def many (p : Parser) : Parser :=
  manyNoAntiquot (withAntiquotSpliceAndSuffix `many p (symbol "*"))

/-- The parser `many1(p)`, or `p+`, repeats `p` until it fails, and returns the list of results.
`p` must succeed at least once, or this parser will fail.

Note that this parser produces the same parse tree as the `many(p)` / `p*` combinator,
and one matches both `p*` and `p+` using `$[ .. ]*` syntax in a syntax match.
(There is no `$[ .. ]+` syntax.)

The argument `p` is "auto-grouped", meaning that if the arity is greater than 1 it will be
automatically replaced by `group(p)` to ensure that it produces exactly 1 value.

This parser has arity 1: it produces a `nullKind` node containing one argument for each
invocation of `p` (or `group(p)`). -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def many1 (p : Parser) : Parser :=
  many1NoAntiquot (withAntiquotSpliceAndSuffix `many p (symbol "*"))

/-- The parser `ident` parses a single identifier, possibly with namespaces, such as `foo` or
`bar.baz`. The identifier must not be a declared token, so for example it will not match `"def"`
because `def` is a keyword token. Tokens are implicitly declared by using them in string literals
in parser declarations, so `syntax foo := "bla"` will make `bla` no longer legal as an identifier.

Identifiers can contain special characters or keywords if they are escaped using the `«»` characters:
`«def»` is an identifier named `def`, and `«x»` is treated the same as `x`. This is useful for
using disallowed characters in identifiers such as `«foo.bar».baz` or `«hello world»`.

This parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.
You can use `TSyntax.getId` to extract the name from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def ident : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) identNoAntiquot

-- `optional (checkNoWsBefore >> "." >> checkNoWsBefore >> ident)`
-- can never fully succeed but ensures that the identifier
-- produces a partial syntax that contains the dot.
-- The partial syntax is sometimes useful for dot-auto-completion.
@[run_builtin_parser_attribute_hooks, builtin_doc] def identWithPartialTrailingDot :=
  ident >> optional (checkNoWsBefore >> "." >> checkNoWsBefore >> ident)

-- `ident` and `rawIdent` produce the same syntax tree, so we reuse the antiquotation kind name
@[run_builtin_parser_attribute_hooks, builtin_doc] def rawIdent : Parser :=
  withAntiquot (mkAntiquot "ident" identKind) rawIdentNoAntiquot

/-- The parser `hygieneInfo` parses no text, but captures the current macro scope information
as though it parsed an identifier at the current position. It returns a `hygieneInfoKind` node
around an `.ident` which is `Name.anonymous` but with macro scopes like a regular identifier.

This is used to implement `have := ...` syntax: the `hygieneInfo` between the `have` and `:=`
substitutes for the identifier which would normally go there as in `have x :=`, so that we
can expand `have :=` to `have this :=` while retaining the usual macro name resolution behavior.
See [doc/macro_overview.md](https://github.com/leanprover/lean4/blob/master/doc/macro_overview.md)
for more information about macro hygiene.

This parser has arity 1: it produces a `Syntax.ident` node containing the parsed identifier.
You can use `TSyntax.getHygieneInfo` to extract the name from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def hygieneInfo : Parser :=
  withAntiquot (mkAntiquot "hygieneInfo" hygieneInfoKind (anonymous := false)) hygieneInfoNoAntiquot

/-- The parser `num` parses a numeric literal in several bases:

* Decimal: `129`
* Hexadecimal: `0xdeadbeef`
* Octal: `0o755`
* Binary: `0b1101`

This parser has arity 1: it produces a `numLitKind` node containing an atom with the text of the
literal.
You can use `TSyntax.getNat` to extract the number from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def numLit : Parser :=
  withAntiquot (mkAntiquot "num" numLitKind) numLitNoAntiquot

/-- The parser `scientific` parses a scientific-notation literal, such as `1.3e-24`.

This parser has arity 1: it produces a `scientificLitKind` node containing an atom with the text
of the literal.
You can use `TSyntax.getScientific` to extract the parts from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def scientificLit : Parser :=
  withAntiquot (mkAntiquot "scientific" scientificLitKind) scientificLitNoAntiquot

/-- The parser `str` parses a string literal, such as `"foo"` or `"\r\n"`. Strings can contain
C-style escapes like `\n`, `\"`, `\x00` or `\u2665`, as well as literal unicode characters like `∈`.
Newlines in a string are interpreted literally.

This parser has arity 1: it produces a `strLitKind` node containing an atom with the raw
literal (including the quote marks and without interpreting the escapes).
You can use `TSyntax.getString` to decode the string from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def strLit : Parser :=
  withAntiquot (mkAntiquot "str" strLitKind) strLitNoAntiquot

/-- The parser `char` parses a character literal, such as `'a'` or `'\n'`. Character literals can
contain C-style escapes like `\n`, `\"`, `\x00` or `\u2665`, as well as literal unicode characters
like `∈`, but must evaluate to a single unicode codepoint, so `'♥'` is allowed but `'❤️'` is not
(since it is two codepoints but one grapheme cluster).

This parser has arity 1: it produces a `charLitKind` node containing an atom with the raw
literal (including the quote marks and without interpreting the escapes).
You can use `TSyntax.getChar` to decode the string from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def charLit : Parser :=
  withAntiquot (mkAntiquot "char" charLitKind) charLitNoAntiquot

/-- The parser `name` parses a name literal like `` `foo``. The syntax is the same as for identifiers
(see `ident`) but with a leading backquote.

This parser has arity 1: it produces a `nameLitKind` node containing the raw literal
(including the backquote).
You can use `TSyntax.getName` to extract the name from the resulting syntax object. -/
@[run_builtin_parser_attribute_hooks, builtin_doc] def nameLit : Parser :=
  withAntiquot (mkAntiquot "name" nameLitKind) nameLitNoAntiquot

/-- The parser `group(p)` parses the same thing as `p`, but it wraps the results in a `groupKind`
node.

This parser always has arity 1, even if `p` does not. Parsers like `p*` are automatically
rewritten to `group(p)*` if `p` does not have arity 1, so that the results from separate invocations
of `p` can be differentiated. -/
@[run_builtin_parser_attribute_hooks, builtin_doc, inline] def group (p : Parser) : Parser :=
  node groupKind p

/-- The parser `many1Indent(p)` is equivalent to `withPosition((colGe p)+)`. This has the effect of
parsing one or more occurrences of `p`, where each subsequent `p` parse needs to be indented
the same or more than the first parse.

This parser has arity 1, and returns a list of the results from `p`.
`p` is "auto-grouped" if it is not arity 1. -/
@[run_builtin_parser_attribute_hooks, builtin_doc, inline] def many1Indent (p : Parser) : Parser :=
  withPosition $ many1 (checkColGe "irrelevant" >> p)

/-- The parser `manyIndent(p)` is equivalent to `withPosition((colGe p)*)`. This has the effect of
parsing zero or more occurrences of `p`, where each subsequent `p` parse needs to be indented
the same or more than the first parse.

This parser has arity 1, and returns a list of the results from `p`.
`p` is "auto-grouped" if it is not arity 1. -/
@[run_builtin_parser_attribute_hooks, builtin_doc, inline] def manyIndent (p : Parser) : Parser :=
  withPosition $ many (checkColGe "irrelevant" >> p)

@[builtin_doc, inline] def sepByIndent (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  withPosition $ sepBy (checkColGe "irrelevant" >> p) sep (psep <|> checkColEq "irrelevant" >> checkLinebreakBefore >> pushNone) allowTrailingSep

@[builtin_doc, inline] def sepBy1Indent (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  withPosition $ sepBy1 (checkColGe "irrelevant" >> p) sep (psep <|> checkColEq "irrelevant" >> checkLinebreakBefore >> pushNone) allowTrailingSep

open PrettyPrinter Syntax.MonadTraverser Formatter in
@[combinator_formatter sepByIndent]
def sepByIndent.formatter (p : Formatter) (_sep : String) (pSep : Formatter) : Formatter := do
  let stx ← getCur
  let hasNewlineSep := stx.getArgs.mapIdx (fun i n =>
    i % 2 == 1 && n.matchesNull 0 && i != stx.getArgs.size - 1) |>.any id
  visitArgs do
    for i in (List.range stx.getArgs.size).reverse do
      if i % 2 == 0 then p else pSep <|>
        -- If the final separator is a newline, skip it.
        ((if i == stx.getArgs.size - 1 then pure () else pushWhitespace "\n") *> goLeft)
  -- If there is any newline separator, then we add an `align` at the start
  -- so that `withPosition` will pick up the right column.
  if hasNewlineSep then
    pushAlign (force := true)

@[combinator_formatter sepBy1Indent] def sepBy1Indent.formatter := sepByIndent.formatter

attribute [run_builtin_parser_attribute_hooks] sepByIndent sepBy1Indent

@[run_builtin_parser_attribute_hooks, builtin_doc] abbrev notSymbol (s : String) : Parser :=
  notFollowedBy (symbol s) s

/-- No-op parser combinator that annotates subtrees to be ignored in syntax patterns. -/
@[run_builtin_parser_attribute_hooks, builtin_doc, inline]
def patternIgnore : Parser → Parser := node `patternIgnore

/-- No-op parser that advises the pretty printer to emit a non-breaking space. -/
@[builtin_doc, inline] def ppHardSpace : Parser := skip
/-- No-op parser that advises the pretty printer to emit a space/soft line break. -/
@[builtin_doc, inline] def ppSpace : Parser := skip
/-- No-op parser that advises the pretty printer to emit a hard line break. -/
@[builtin_doc, inline] def ppLine : Parser := skip
/-- No-op parser combinator that advises the pretty printer to emit a `Format.fill` node. -/
@[builtin_doc, inline] def ppRealFill : Parser → Parser := id
/-- No-op parser combinator that advises the pretty printer to emit a `Format.group` node. -/
@[builtin_doc, inline] def ppRealGroup : Parser → Parser := id
/-- No-op parser combinator that advises the pretty printer to indent the given syntax without grouping it. -/
@[builtin_doc, inline] def ppIndent : Parser → Parser := id
/--
  No-op parser combinator that advises the pretty printer to group and indent the given syntax.
  By default, only syntax categories are grouped. -/
@[builtin_doc, inline] def ppGroup (p : Parser) : Parser := ppRealFill (ppIndent p)
/--
  No-op parser combinator that advises the pretty printer to dedent the given syntax.
  Dedenting can in particular be used to counteract automatic indentation. -/
@[builtin_doc, inline] def ppDedent : Parser → Parser := id

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
@[builtin_doc, inline] def ppAllowUngrouped : Parser := skip

/--
  No-op parser combinator that advises the pretty printer to dedent the given syntax,
  if it was grouped by the category parser.
  Dedenting can in particular be used to counteract automatic indentation. -/
@[builtin_doc, inline] def ppDedentIfGrouped : Parser → Parser := id

/--
  No-op parser combinator that prints a line break.
  The line break is soft if the combinator is followed
  by an ungrouped parser (see ppAllowUngrouped), otherwise hard. -/
@[builtin_doc, inline] def ppHardLineUnlessUngrouped : Parser := skip

end Parser

section
open PrettyPrinter Parser

@[combinator_formatter ppHardSpace] def ppHardSpace.formatter : Formatter := Formatter.pushWhitespace " "
@[combinator_formatter ppSpace] def ppSpace.formatter : Formatter := Formatter.pushLine
@[combinator_formatter ppLine] def ppLine.formatter : Formatter := Formatter.pushWhitespace "\n"
@[combinator_formatter ppRealFill] def ppRealFill.formatter (p : Formatter) : Formatter := Formatter.fill p
@[combinator_formatter ppRealGroup] def ppRealGroup.formatter (p : Formatter) : Formatter := Formatter.group p
@[combinator_formatter ppIndent] def ppIndent.formatter (p : Formatter) : Formatter := Formatter.indent p
@[combinator_formatter ppDedent] def ppDedent.formatter (p : Formatter) : Formatter := do
  let opts ← getOptions
  Formatter.indent p (some ((0:Int) - Std.Format.getIndent opts))

@[combinator_formatter ppAllowUngrouped] def ppAllowUngrouped.formatter : Formatter := do
  modify ({ · with mustBeGrouped := false })
@[combinator_formatter ppDedentIfGrouped] def ppDedentIfGrouped.formatter (p : Formatter) : Formatter := do
  Formatter.concat p
  let indent := Std.Format.getIndent (← getOptions)
  unless (← get).isUngrouped do
    modify fun st => { st with stack := st.stack.modify (st.stack.size - 1) (·.nest (0 - indent)) }
@[combinator_formatter ppHardLineUnlessUngrouped] def ppHardLineUnlessUngrouped.formatter : Formatter := do
  if (← get).isUngrouped then
    Formatter.pushLine
  else
    ppLine.formatter

end

namespace Parser

-- now synthesize parenthesizers
attribute [run_builtin_parser_attribute_hooks]
  ppHardSpace ppSpace ppLine ppGroup ppRealGroup ppRealFill ppIndent ppDedent
  ppAllowUngrouped ppDedentIfGrouped ppHardLineUnlessUngrouped

syntax "register_parser_alias " group("(" &"kind" " := " term ") ")? (strLit ppSpace)? ident (ppSpace colGt term)? : term
macro_rules
  | `(register_parser_alias $[(kind := $kind?)]? $(aliasName?)? $declName $(info?)?) => do
    let [(fullDeclName, [])] ← Macro.resolveGlobalName declName.getId |
      Macro.throwError "expected non-overloaded constant name"
    let aliasName := match aliasName? with
      | some n => quote (Name.mkSimple n.getString)
      | none => quote declName.getId
    `(do Parser.registerAlias $aliasName ``$declName $declName $(info?.getD (Unhygienic.run `({}))) (kind? := some $(kind?.getD (quote fullDeclName)))
         PrettyPrinter.Formatter.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `formatter))
         PrettyPrinter.Parenthesizer.registerAlias $aliasName $(mkIdentFrom declName (declName.getId ++ `parenthesizer)))

builtin_initialize
  register_parser_alias patternIgnore { autoGroupArgs := false }

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
