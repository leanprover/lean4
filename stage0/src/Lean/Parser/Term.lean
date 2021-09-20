/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Attr
import Lean.Parser.Level

namespace Lean
namespace Parser

namespace Command
def commentBody : Parser :=
{ fn := rawFn (finishCommentBlock 1) (trailingWs := true) }

@[combinatorParenthesizer Lean.Parser.Command.commentBody] def commentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinatorFormatter Lean.Parser.Command.commentBody] def commentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def docComment       := leading_parser ppDedent $ "/--" >> commentBody >> ppLine
end Command

builtin_initialize
  registerBuiltinParserAttribute `builtinTacticParser `tactic LeadingIdentBehavior.both
  registerBuiltinDynamicParserAttribute `tacticParser `tactic

@[inline] def tacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `tactic rbp

@[inline] def convParser (rbp : Nat := 0) : Parser :=
  categoryParser `conv rbp

namespace Tactic

def tacticSeq1Indented : Parser :=
  leading_parser many1Indent (group (ppLine >> tacticParser >> optional ";"))
def tacticSeqBracketed : Parser :=
  leading_parser "{" >> many (group (ppLine >> tacticParser >> optional ";")) >> ppDedent (ppLine >> "}")
def tacticSeq :=
  nodeWithAntiquot "tacticSeq" `Lean.Parser.Tactic.tacticSeq (tacticSeqBracketed <|> tacticSeq1Indented)

/- Raw sequence for quotation and grouping -/
def seq1 :=
  node `Lean.Parser.Tactic.seq1 $ sepBy1 tacticParser ";\n" (allowTrailingSep := true)

end Tactic

def darrow : Parser := " => "

namespace Term

/- Built-in parsers -/

@[builtinTermParser] def byTactic := leading_parser:leadPrec "by " >> Tactic.tacticSeq

def optSemicolon (p : Parser) : Parser := ppDedent $ optional ";" >> ppLine >> p

-- `checkPrec` necessary for the pretty printer
@[builtinTermParser] def ident := checkPrec maxPrec >> Parser.ident
@[builtinTermParser] def num : Parser := checkPrec maxPrec >> numLit
@[builtinTermParser] def scientific : Parser := checkPrec maxPrec >> scientificLit
@[builtinTermParser] def str : Parser := checkPrec maxPrec >> strLit
@[builtinTermParser] def char : Parser := checkPrec maxPrec >> charLit
@[builtinTermParser] def type := leading_parser "Type" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
@[builtinTermParser] def sort := leading_parser "Sort" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
@[builtinTermParser] def prop := leading_parser "Prop"
@[builtinTermParser] def hole := leading_parser "_"
@[builtinTermParser] def syntheticHole := leading_parser "?" >> (ident <|> hole)
@[builtinTermParser] def «sorry» := leading_parser "sorry"
@[builtinTermParser] def cdot   := leading_parser symbol "·" <|> "."
def typeAscription := leading_parser " : " >> termParser
def tupleTail      := leading_parser ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := leading_parser "(" >> ppDedent (withoutPosition (withoutForbidden (optional (termParser >> parenSpecial)))) >> ")"
@[builtinTermParser] def anonymousCtor := leading_parser "⟨" >> sepBy termParser ", " >> "⟩"
def optIdent : Parser := optional (atomic (ident >> " : "))
def fromTerm   := leading_parser " from " >> termParser
def sufficesDecl := leading_parser optIdent >> termParser >> (fromTerm <|> byTactic)
@[builtinTermParser] def «suffices» := leading_parser:leadPrec withPosition ("suffices " >> sufficesDecl) >> optSemicolon termParser
@[builtinTermParser] def «show»     := leading_parser:leadPrec "show " >> termParser >> (fromTerm <|> byTactic)
def structInstArrayRef := leading_parser "[" >> termParser >>"]"
def structInstLVal   := leading_parser (ident <|> fieldIdx <|> structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := ppGroup $ leading_parser structInstLVal >> " := " >> termParser
def structInstFieldAbbrev := leading_parser atomic (ident >> notFollowedBy ("." <|> ":=" <|> symbol "[") "invalid field abbreviation") -- `x` is an abbreviation for `x := x`
def optEllipsis      := leading_parser optional ".."
@[builtinTermParser] def structInst := leading_parser "{" >> ppHardSpace >> optional (atomic (sepBy1 termParser ", " >> " with "))
  >> manyIndent (group ((structInstFieldAbbrev <|> structInstField) >> optional ", "))
  >> optEllipsis
  >> optional (" : " >> termParser) >> " }"
def typeSpec := leading_parser " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def explicit := leading_parser "@" >> termParser maxPrec
@[builtinTermParser] def inaccessible := leading_parser ".(" >> termParser >> ")"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then node nullKind (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := leading_parser atomic (symbol " := " >> " by ") >> Tactic.tacticSeq
def binderDefault := leading_parser " := " >> termParser
def explicitBinder (requireType := false) := ppGroup $ leading_parser "(" >> many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault) >> ")"
def implicitBinder (requireType := false) := ppGroup $ leading_parser "{" >> many1 binderIdent >> binderType requireType >> "}"
def strictImplicitLeftBracket := atomic (group (symbol "{" >> "{")) <|> "⦃"
def strictImplicitRightBracket := atomic (group (symbol "}" >> "}")) <|> "⦄"
def strictImplicitBinder (requireType := false) := ppGroup $ leading_parser strictImplicitLeftBracket >> many1 binderIdent >> binderType requireType >> strictImplicitRightBracket
def instBinder := ppGroup $ leading_parser "[" >> optIdent >> termParser >> "]"
def bracketedBinder (requireType := false) := withAntiquot (mkAntiquot "bracketedBinder" none (anonymous := false)) <|
  explicitBinder requireType <|> strictImplicitBinder requireType <|> implicitBinder requireType <|> instBinder

/-
It is feasible to support dependent arrows such as `{α} → α → α` without sacrificing the quality of the error messages for the longer case.
`{α} → α → α` would be short for `{α : Type} → α → α`
Here is the encoding:
```
def implicitShortBinder := node `Lean.Parser.Term.implicitBinder $ "{" >> many1 binderIdent >> pushNone >> "}"
def depArrowShortPrefix := try (implicitShortBinder >> unicodeSymbol " → " " -> ")
def depArrowLongPrefix  := bracketedBinder true >> unicodeSymbol " → " " -> "
def depArrowPrefix      := depArrowShortPrefix <|> depArrowLongPrefix
@[builtinTermParser] def depArrow := leading_parser depArrowPrefix >> termParser
```
Note that no changes in the elaborator are needed.
We decided to not use it because terms such as `{α} → α → α` may look too cryptic.
Note that we did not add a `explicitShortBinder` parser since `(α) → α → α` is really cryptic as a short for `(α : Type) → α → α`.
-/
@[builtinTermParser] def depArrow := leading_parser:25 bracketedBinder true >> unicodeSymbol " → " " -> " >> termParser

def simpleBinder := leading_parser many1 binderIdent >> optType
@[builtinTermParser]
def «forall» := leading_parser:leadPrec unicodeSymbol "∀" "forall" >> many1 (ppSpace >> (simpleBinder <|> bracketedBinder)) >> ", " >> termParser

def matchAlt (rhsParser : Parser := termParser) : Parser :=
  nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
    "| " >> ppIndent (sepBy1 termParser ", " >> darrow >> checkColGe "alternative right-hand-side to start in a column greater than or equal to the corresponding '|'" >> rhsParser)
/--
  Useful for syntax quotations. Note that generic patterns such as `` `(matchAltExpr| | ... => $rhs) `` should also
  work with other `rhsParser`s (of arity 1). -/
def matchAltExpr := matchAlt

def matchAlts (rhsParser : Parser := termParser) : Parser :=
  leading_parser ppDedent $ withPosition $ many1Indent (ppLine >> matchAlt rhsParser)

def matchDiscr := leading_parser optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> termParser

def trueVal  := leading_parser nonReservedSymbol "true"
def falseVal := leading_parser nonReservedSymbol "false"
def generalizingParam := leading_parser atomic ("(" >> nonReservedSymbol "generalizing") >> " := " >> (trueVal <|> falseVal)  >> ")"

@[builtinTermParser] def «match» := leading_parser:leadPrec "match " >> optional generalizingParam >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
@[builtinTermParser] def «nomatch» := leading_parser:leadPrec "nomatch " >> termParser

def funImplicitBinder := atomic (lookahead ("{" >> many1 binderIdent >> (symbol " : " <|> "}"))) >> implicitBinder
def funStrictImplicitBinder := atomic (lookahead (strictImplicitLeftBracket >> many1 binderIdent >> (symbol " : " <|> strictImplicitRightBracket))) >> strictImplicitBinder
def funSimpleBinder   := atomic (lookahead (many1 binderIdent >> " : ")) >> simpleBinder
def funBinder : Parser := funStrictImplicitBinder <|> funImplicitBinder <|> instBinder <|> funSimpleBinder <|> termParser maxPrec
-- NOTE: we use `nodeWithAntiquot` to ensure that `fun $b => ...` remains a `term` antiquotation
def basicFun : Parser := nodeWithAntiquot "basicFun" `Lean.Parser.Term.basicFun (many1 (ppSpace >> funBinder) >> darrow >> termParser)
@[builtinTermParser] def «fun» := leading_parser:maxPrec unicodeSymbol "λ" "fun" >> (basicFun <|> matchAlts)

def optExprPrecedence := optional (atomic ":" >> termParser maxPrec)
@[builtinTermParser] def «leading_parser»  := leading_parser:leadPrec "leading_parser " >> optExprPrecedence >> termParser
@[builtinTermParser] def «trailing_parser» := leading_parser:leadPrec "trailing_parser " >> optExprPrecedence >> optExprPrecedence >> termParser

@[builtinTermParser] def borrowed   := leading_parser "@&" >> termParser leadPrec
@[builtinTermParser] def quotedName := leading_parser nameLit
-- use `rawCh` because ``"`" >> ident`` overlaps with `nameLit`, with the latter being preferred by the tokenizer
-- note that we cannot use ```"``"``` as a new token either because it would break `precheckedQuot`
@[builtinTermParser] def doubleQuotedName := leading_parser "`" >> checkNoWsBefore >> rawCh '`' (trailingWs := false) >> ident

def simpleBinderWithoutType := nodeWithAntiquot "simpleBinder" `Lean.Parser.Term.simpleBinder (anonymous := true)
  (many1 binderIdent >> pushNone)

/- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser := ident >> checkWsBefore "expected space before binders" >> many (ppSpace >> (simpleBinderWithoutType <|> bracketedBinder)) >> optType
def letIdDecl   := nodeWithAntiquot "letIdDecl"   `Lean.Parser.Term.letIdDecl   $ atomic (letIdLhs >> " := ") >> termParser
def letPatDecl  := nodeWithAntiquot "letPatDecl"  `Lean.Parser.Term.letPatDecl  $ atomic (termParser >> pushNone >> optType >> " := ") >> termParser
def letEqnsDecl := nodeWithAntiquot "letEqnsDecl" `Lean.Parser.Term.letEqnsDecl $ letIdLhs >> matchAlts
-- Remark: we use `nodeWithAntiquot` here to make sure anonymous antiquotations (e.g., `$x`) are not `letDecl`
def letDecl     := nodeWithAntiquot "letDecl" `Lean.Parser.Term.letDecl (notFollowedBy (nonReservedSymbol "rec") "rec" >> (letIdDecl <|> letPatDecl <|> letEqnsDecl))
@[builtinTermParser] def «let» := leading_parser:leadPrec  withPosition ("let " >> letDecl) >> optSemicolon termParser
@[builtinTermParser] def «let_fun»     := leading_parser:leadPrec withPosition ((symbol "let_fun " <|> "let_λ") >> letDecl) >> optSemicolon termParser
@[builtinTermParser] def «let_delayed» := leading_parser:leadPrec withPosition ("let_delayed " >> letDecl) >> optSemicolon termParser

-- like `let_fun` but with optional name
def haveIdLhs    := optional (ident >> many (ppSpace >> (simpleBinderWithoutType <|> bracketedBinder))) >> optType
def haveIdDecl   := nodeWithAntiquot "haveIdDecl"   `Lean.Parser.Term.haveIdDecl   $ atomic (haveIdLhs >> " := ") >> termParser
def haveEqnsDecl := nodeWithAntiquot "haveEqnsDecl" `Lean.Parser.Term.haveEqnsDecl $ haveIdLhs >> matchAlts
def haveDecl     := nodeWithAntiquot "haveDecl" `Lean.Parser.Term.haveDecl (haveIdDecl <|> letPatDecl <|> haveEqnsDecl)
@[builtinTermParser] def «have» := leading_parser:leadPrec withPosition ("have " >> haveDecl) >> optSemicolon termParser

def «scoped» := leading_parser "scoped "
def «local»  := leading_parser "local "
def attrKind := leading_parser optional («scoped» <|> «local»)
def attrInstance     := ppGroup $ leading_parser attrKind >> attrParser

def attributes       := leading_parser "@[" >> sepBy1 attrInstance ", " >> "]"
def letRecDecl       := leading_parser optional Command.docComment >> optional «attributes» >> letDecl
def letRecDecls      := leading_parser sepBy1 letRecDecl ", "
@[builtinTermParser]
def «letrec» := leading_parser:leadPrec withPosition (group ("let " >> nonReservedSymbol "rec ") >> letRecDecls) >> optSemicolon termParser

@[runBuiltinParserAttributeHooks]
def whereDecls := leading_parser "where " >> many1Indent (group (letRecDecl >> optional ";"))
@[runBuiltinParserAttributeHooks]
def matchAltsWhereDecls := leading_parser matchAlts >> optional whereDecls

@[builtinTermParser] def noindex := leading_parser "no_index " >> termParser maxPrec

@[builtinTermParser] def binrel := leading_parser "binrel% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec
@[builtinTermParser] def binop  := leading_parser "binop% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec
@[builtinTermParser] def binop_lazy  := leading_parser "binop_lazy% " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec

@[builtinTermParser] def forInMacro := leading_parser "forIn% " >> termParser maxPrec >> termParser maxPrec >> termParser maxPrec

@[builtinTermParser] def typeOf             := leading_parser "typeOf% " >> termParser maxPrec
@[builtinTermParser] def ensureTypeOf       := leading_parser "ensureTypeOf% " >> termParser maxPrec >> strLit >> termParser
@[builtinTermParser] def ensureExpectedType := leading_parser "ensureExpectedType% " >> strLit >> termParser maxPrec
@[builtinTermParser] def noImplicitLambda   := leading_parser "noImplicitLambda% " >> termParser maxPrec

def namedArgument  := leading_parser atomic ("(" >> ident >> " := ") >> termParser >> ")"
def ellipsis       := leading_parser ".."
def argument       :=
  checkWsBefore "expected space" >>
  checkColGt "expected to be indented" >>
  (namedArgument <|> ellipsis <|> termParser argPrec)
-- `app` precedence is `lead` (cannot be used as argument)
-- `lhs` precedence is `max` (i.e. does not accept `arg` precedence)
-- argument precedence is `arg` (i.e. does not accept `lead` precedence)
@[builtinTermParser] def app      := trailing_parser:leadPrec:maxPrec many1 argument

@[builtinTermParser] def proj     := trailing_parser checkNoWsBefore >> "." >> checkNoWsBefore >> (fieldIdx <|> ident)
@[builtinTermParser] def completion := trailing_parser checkNoWsBefore >> "."
@[builtinTermParser] def arrayRef := trailing_parser checkNoWsBefore >> "[" >> termParser >>"]"
@[builtinTermParser] def arrow    := trailing_parser checkPrec 25 >> unicodeSymbol " → " " -> " >> termParser 25

def isIdent (stx : Syntax) : Bool :=
  -- antiquotations should also be allowed where an identifier is expected
  stx.isAntiquot || stx.isIdent

@[builtinTermParser] def explicitUniv : TrailingParser := trailing_parser checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '.{'" >> ".{" >> sepBy1 levelParser ", " >> "}"
@[builtinTermParser] def namedPattern : TrailingParser := trailing_parser checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '@'" >> "@" >> termParser maxPrec

@[builtinTermParser] def pipeProj   := trailing_parser:minPrec " |>." >> checkNoWsBefore >> (fieldIdx <|> ident) >> many argument
@[builtinTermParser] def pipeCompletion := trailing_parser:minPrec " |>."

@[builtinTermParser] def subst := trailing_parser:75 " ▸ " >> sepBy1 (termParser 75) " ▸ "

-- NOTE: Doesn't call `categoryParser` directly in contrast to most other "static" quotations, so call `evalInsideQuot` explicitly
@[builtinTermParser] def funBinder.quot : Parser := leading_parser "`(funBinder|"  >> incQuotDepth (evalInsideQuot ``funBinder funBinder) >> ")"
def bracketedBinderF := bracketedBinder  -- no default arg
@[builtinTermParser] def bracketedBinder.quot : Parser := leading_parser "`(bracketedBinder|"  >> incQuotDepth (evalInsideQuot ``bracketedBinderF bracketedBinder) >> ")"
@[builtinTermParser] def matchDiscr.quot : Parser := leading_parser "`(matchDiscr|"  >> incQuotDepth (evalInsideQuot ``matchDiscr matchDiscr) >> ")"
@[builtinTermParser] def attr.quot : Parser := leading_parser "`(attr|"  >> incQuotDepth attrParser >> ")"

@[builtinTermParser] def panic       := leading_parser:leadPrec "panic! " >> termParser
@[builtinTermParser] def unreachable := leading_parser:leadPrec "unreachable!"
@[builtinTermParser] def dbgTrace    := leading_parser:leadPrec withPosition ("dbg_trace" >> ((interpolatedStr termParser) <|> termParser)) >> optSemicolon termParser
@[builtinTermParser] def assert      := leading_parser:leadPrec withPosition ("assert! " >> termParser) >> optSemicolon termParser


def macroArg       := termParser maxPrec
def macroDollarArg := leading_parser "$" >> termParser 10
def macroLastArg   := macroDollarArg <|> macroArg

-- Macro for avoiding exponentially big terms when using `STWorld`
@[builtinTermParser] def stateRefT   := leading_parser "StateRefT" >> macroArg >> macroLastArg

@[builtinTermParser] def dynamicQuot := leading_parser "`(" >> ident >> "|" >> incQuotDepth (parserOfStack 1) >> ")"

end Term

@[builtinTermParser default+1] def Tactic.quot    : Parser := leading_parser "`(tactic|" >> incQuotDepth tacticParser >> ")"
@[builtinTermParser] def Tactic.quotSeq : Parser := leading_parser "`(tactic|" >> incQuotDepth Tactic.seq1 >> ")"

@[builtinTermParser] def Level.quot  : Parser := leading_parser "`(level|" >> incQuotDepth levelParser >> ")"

open Term in
builtin_initialize
  register_parser_alias letDecl
  register_parser_alias haveDecl
  register_parser_alias sufficesDecl
  register_parser_alias letRecDecls
  register_parser_alias hole
  register_parser_alias syntheticHole
  register_parser_alias matchDiscr
  register_parser_alias bracketedBinder
  register_parser_alias attrKind

end Parser
end Lean
