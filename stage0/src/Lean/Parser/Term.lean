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
{ fn := rawFn (finishCommentBlock 1) true }

@[combinatorParenthesizer Lean.Parser.Command.commentBody] def commentBody.parenthesizer := PrettyPrinter.Parenthesizer.visitToken
@[combinatorFormatter Lean.Parser.Command.commentBody] def commentBody.formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

def docComment       := parser! ppDedent $ "/--" >> commentBody >> ppLine
end Command

builtin_initialize
  registerBuiltinParserAttribute `builtinTacticParser `tactic LeadingIdentBehavior.both
  registerBuiltinDynamicParserAttribute `tacticParser `tactic

@[inline] def tacticParser (rbp : Nat := 0) : Parser :=
  categoryParser `tactic rbp

namespace Tactic

def tacticSeq1Indented : Parser :=
  parser! many1Indent (group (ppLine >> tacticParser >> optional ";"))
def tacticSeqBracketed : Parser :=
  parser! "{" >> many (group (ppLine >> tacticParser >> optional ";")) >> ppDedent (ppLine >> "}")
def tacticSeq :=
  nodeWithAntiquot "tacticSeq" `Lean.Parser.Tactic.tacticSeq (tacticSeqBracketed <|> tacticSeq1Indented)

/- Raw sequence for quotation and grouping -/
def seq1 :=
  node `Lean.Parser.Tactic.seq1 $ sepBy1 tacticParser ";\n" (allowTrailingSep := true)

end Tactic

def darrow : Parser := " => "

namespace Term

/- Built-in parsers -/

@[builtinTermParser] def byTactic := parser!:leadPrec "by " >> Tactic.tacticSeq

def optSemicolon (p : Parser) : Parser := ppDedent $ optional ";" >> ppLine >> p

-- `checkPrec` necessary for the pretty printer
@[builtinTermParser] def ident := checkPrec maxPrec >> Parser.ident
@[builtinTermParser] def num : Parser := checkPrec maxPrec >> numLit
@[builtinTermParser] def scientific : Parser := checkPrec maxPrec >> scientificLit
@[builtinTermParser] def str : Parser := checkPrec maxPrec >> strLit
@[builtinTermParser] def char : Parser := checkPrec maxPrec >> charLit
@[builtinTermParser] def type := parser! "Type" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
@[builtinTermParser] def sort := parser! "Sort" >> optional (checkWsBefore "" >> checkPrec leadPrec >> checkColGt >> levelParser maxPrec)
@[builtinTermParser] def prop := parser! "Prop"
@[builtinTermParser] def hole := parser! "_"
@[builtinTermParser] def syntheticHole := parser! "?" >> (ident <|> hole)
@[builtinTermParser] def «sorry» := parser! "sorry"
@[builtinTermParser] def cdot   := parser! symbol "·" <|> "."
@[builtinTermParser] def emptyC := parser! "∅" <|> (symbol "{" >> "}")
def typeAscription := parser! " : " >> termParser
def tupleTail      := parser! ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := parser! "(" >> ppDedent (withoutPosition (withoutForbidden (optional (termParser >> parenSpecial)))) >> ")"
@[builtinTermParser] def anonymousCtor := parser! "⟨" >> sepBy termParser ", " >> "⟩"
def optIdent : Parser := optional (atomic (ident >> " : "))
def fromTerm   := parser! " from " >> termParser
def haveAssign := parser! " := " >> termParser
def haveDecl   := optIdent >> termParser >> (haveAssign <|> fromTerm <|> byTactic)
@[builtinTermParser] def «have» := parser!:leadPrec withPosition ("have " >> haveDecl) >> optSemicolon termParser
def sufficesDecl := optIdent >> termParser >> (fromTerm <|> byTactic)
@[builtinTermParser] def «suffices» := parser!:leadPrec withPosition ("suffices " >> sufficesDecl) >> optSemicolon termParser
@[builtinTermParser] def «show»     := parser!:leadPrec "show " >> termParser >> (fromTerm <|> byTactic)
def structInstArrayRef := parser! "[" >> termParser >>"]"
def structInstLVal   := parser! (ident <|> fieldIdx <|> structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := ppGroup $ parser! structInstLVal >> " := " >> termParser
def optEllipsis      := parser! optional ".."
@[builtinTermParser] def structInst := parser! "{" >> ppHardSpace >> optional (atomic (termParser >> " with "))
  >> manyIndent (group (structInstField >> optional ", "))
  >> optEllipsis
  >> optional (" : " >> termParser) >> " }"
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def explicit := parser! "@" >> termParser maxPrec
@[builtinTermParser] def inaccessible := parser! ".(" >> termParser >> ")"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then group (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := parser! atomic (symbol " := " >> " by ") >> Tactic.tacticSeq
def binderDefault := parser! " := " >> termParser
def explicitBinder (requireType := false) := ppGroup $ parser! "(" >> many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault) >> ")"
def implicitBinder (requireType := false) := ppGroup $ parser! "{" >> many1 binderIdent >> binderType requireType >> "}"
def instBinder := ppGroup $ parser! "[" >> optIdent >> termParser >> "]"
def bracketedBinder (requireType := false) := withAntiquot (mkAntiquot "bracketedBinder" none (anonymous := false)) <|
  explicitBinder requireType <|> implicitBinder requireType <|> instBinder

/-
It is feasible to support dependent arrows such as `{α} → α → α` without sacrificing the quality of the error messages for the longer case.
`{α} → α → α` would be short for `{α : Type} → α → α`
Here is the encoding:
```
def implicitShortBinder := node `Lean.Parser.Term.implicitBinder $ "{" >> many1 binderIdent >> pushNone >> "}"
def depArrowShortPrefix := try (implicitShortBinder >> unicodeSymbol " → " " -> ")
def depArrowLongPrefix  := bracketedBinder true >> unicodeSymbol " → " " -> "
def depArrowPrefix      := depArrowShortPrefix <|> depArrowLongPrefix
@[builtinTermParser] def depArrow := parser! depArrowPrefix >> termParser
```
Note that no changes in the elaborator are needed.
We decided to not use it because terms such as `{α} → α → α` may look too cryptic.
Note that we did not add a `explicitShortBinder` parser since `(α) → α → α` is really cryptic as a short for `(α : Type) → α → α`.
-/
@[builtinTermParser] def depArrow := parser!:25 bracketedBinder true >> unicodeSymbol " → " " -> " >> termParser

def simpleBinder := parser! many1 binderIdent >> optType
@[builtinTermParser]
def «forall» := parser!:leadPrec unicodeSymbol "∀" "forall" >> many1 (ppSpace >> (simpleBinder <|> bracketedBinder)) >> ", " >> termParser

def matchAlt (rhsParser : Parser := termParser) : Parser :=
  nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
    "| " >> ppIndent (sepBy1 termParser ", " >> darrow >> rhsParser)
/--
  Useful for syntax quotations. Note that generic patterns such as `` `(matchAltExpr| | ... => $rhs) `` should also
  work with other `rhsParser`s (of arity 1). -/
def matchAltExpr := matchAlt

def matchAlts (rhsParser : Parser := termParser) : Parser :=
  parser! ppDedent $ withPosition $ many1Indent (ppLine >> matchAlt rhsParser)

def matchDiscr := parser! optional (atomic (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> termParser

@[builtinTermParser] def «match» := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
@[builtinTermParser] def «nomatch»  := parser!:leadPrec "nomatch " >> termParser

def funImplicitBinder := atomic (lookahead ("{" >> many1 binderIdent >> (symbol " : " <|> "}"))) >> implicitBinder
def funSimpleBinder   := atomic (lookahead (many1 binderIdent >> " : ")) >> simpleBinder
def funBinder : Parser := funImplicitBinder <|> instBinder <|> funSimpleBinder <|> termParser maxPrec
-- NOTE: we use `nodeWithAntiquot` to ensure that `fun $b => ...` remains a `term` antiquotation
def basicFun : Parser := nodeWithAntiquot "basicFun" `Lean.Parser.Term.basicFun (many1 (ppSpace >> funBinder) >> darrow >> termParser)
@[builtinTermParser] def «fun» := parser!:maxPrec unicodeSymbol "λ" "fun" >> (basicFun <|> matchAlts)

def optExprPrecedence := optional (atomic ":" >> termParser maxPrec)
@[builtinTermParser] def «parser!»  := parser!:leadPrec "parser! " >> optExprPrecedence >> termParser
@[builtinTermParser] def «tparser!» := parser!:leadPrec "tparser! " >> optExprPrecedence >> termParser
@[builtinTermParser] def borrowed   := parser! "@&" >> termParser leadPrec
@[builtinTermParser] def quotedName := parser! nameLit
@[builtinTermParser] def doubleQuotedName := parser! "`" >> checkNoWsBefore >> nameLit

def simpleBinderWithoutType := nodeWithAntiquot "simpleBinder" `Lean.Parser.Term.simpleBinder (anonymous := true)
  (many1 binderIdent >> pushNone)

/- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser := ident >> checkWsBefore "expected space before binders" >> many (ppSpace >> (simpleBinderWithoutType <|> bracketedBinder)) >> optType
def letIdDecl   := nodeWithAntiquot "letIdDecl"   `Lean.Parser.Term.letIdDecl   $ atomic (letIdLhs >> " := ") >> termParser
def letPatDecl  := nodeWithAntiquot "letPatDecl"  `Lean.Parser.Term.letPatDecl  $ atomic (termParser >> pushNone >> optType >> " := ") >> termParser
def letEqnsDecl := nodeWithAntiquot "letEqnsDecl" `Lean.Parser.Term.letEqnsDecl $ letIdLhs >> matchAlts
-- Remark: we use `nodeWithAntiquot` here to make sure anonymous antiquotations (e.g., `$x`) are not `letDecl`
def letDecl     := nodeWithAntiquot "letDecl" `Lean.Parser.Term.letDecl (notFollowedBy (nonReservedSymbol "rec") "rec" >> (letIdDecl <|> letPatDecl <|> letEqnsDecl))
@[builtinTermParser] def «let» := parser!:leadPrec  withPosition ("let " >> letDecl) >> optSemicolon termParser
@[builtinTermParser] def «let!» := parser!:leadPrec withPosition ("let! " >> letDecl) >> optSemicolon termParser
@[builtinTermParser] def «let*» := parser!:leadPrec withPosition ("let* " >> letDecl) >> optSemicolon termParser
def «scoped» := parser! "scoped "
def «local»  := parser! "local "
def attrKind := parser! optional («scoped» <|> «local»)
def attrInstance     := ppGroup $ parser! attrKind >> attrParser

def attributes       := parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def letRecDecl       := parser! optional Command.docComment >> optional «attributes» >> letDecl
def letRecDecls      := sepBy1 letRecDecl ", "
@[builtinTermParser]
def «letrec» := parser!:leadPrec withPosition (group ("let " >> nonReservedSymbol "rec ") >> letRecDecls) >> optSemicolon termParser

@[runBuiltinParserAttributeHooks]
def whereDecls := parser! "where " >> many1Indent (group (letRecDecl >> optional ";"))
@[runBuiltinParserAttributeHooks]
def matchAltsWhereDecls := parser! matchAlts >> optional whereDecls

@[builtinTermParser] def nativeRefl   := parser! "nativeRefl! " >> termParser maxPrec
@[builtinTermParser] def nativeDecide := parser! "nativeDecide!"
@[builtinTermParser] def decide       := parser! "decide!"

@[builtinTermParser] def noindex := parser! "noindex!" >> termParser maxPrec

@[builtinTermParser] def binrel  := parser! "binrel! " >> ident >> ppSpace >> termParser maxPrec >> termParser maxPrec

@[builtinTermParser] def typeOf             := parser! "typeOf! " >> termParser maxPrec
@[builtinTermParser] def ensureTypeOf       := parser! "ensureTypeOf! " >> termParser maxPrec >> strLit >> termParser
@[builtinTermParser] def ensureExpectedType := parser! "ensureExpectedType! " >> strLit >> termParser maxPrec

def namedArgument  := parser! atomic ("(" >> ident >> " := ") >> termParser >> ")"
def ellipsis       := parser! ".."
@[builtinTermParser] def app      := tparser!:(maxPrec-1) many1 $
  checkWsBefore "expected space" >>
  checkColGt "expected to be indented" >>
  (namedArgument <|> ellipsis <|> termParser maxPrec)

@[builtinTermParser] def proj     := tparser! checkNoWsBefore >> "." >> (fieldIdx <|> ident)
@[builtinTermParser] def arrayRef := tparser! checkNoWsBefore >> "[" >> termParser >>"]"
@[builtinTermParser] def arrow    := tparser! checkPrec 25 >> unicodeSymbol " → " " -> " >> termParser 25

def isIdent (stx : Syntax) : Bool :=
  -- antiquotations should also be allowed where an identifier is expected
  stx.isAntiquot || stx.isIdent

@[builtinTermParser] def explicitUniv : TrailingParser := tparser! checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '.{'" >> ".{" >> sepBy1 levelParser ", " >> "}"
@[builtinTermParser] def namedPattern : TrailingParser := tparser! checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '@'" >> "@" >> termParser maxPrec

@[builtinTermParser] def pipeProj   := tparser!:minPrec " |>. " >> (fieldIdx <|> ident)

@[builtinTermParser] def subst := tparser!:75 " ▸ " >> sepBy1 (termParser 75) " ▸ "

-- NOTE: Doesn't call `categoryParser` directly in contrast to most other "static" quotations, so call `evalInsideQuot` explicitly
@[builtinTermParser] def funBinder.quot : Parser := parser! "`(funBinder|"  >> toggleInsideQuot (evalInsideQuot ``funBinder funBinder) >> ")"
def bracketedBinderF := bracketedBinder  -- no default arg
@[builtinTermParser] def bracketedBinder.quot : Parser := parser! "`(bracketedBinder|"  >> toggleInsideQuot (evalInsideQuot ``bracketedBinderF bracketedBinder) >> ")"
@[builtinTermParser] def matchDiscr.quot : Parser := parser! "`(matchDiscr|"  >> toggleInsideQuot (evalInsideQuot ``matchDiscr matchDiscr) >> ")"
@[builtinTermParser] def attr.quot : Parser := parser! "`(attr|"  >> toggleInsideQuot attrParser >> ")"

@[builtinTermParser] def panic       := parser!:leadPrec "panic! " >> termParser
@[builtinTermParser] def unreachable := parser!:leadPrec "unreachable!"
@[builtinTermParser] def dbgTrace    := parser!:leadPrec withPosition ("dbgTrace! " >> ((interpolatedStr termParser) <|> termParser)) >> optSemicolon termParser
@[builtinTermParser] def assert      := parser!:leadPrec withPosition ("assert! " >> termParser) >> optSemicolon termParser

def macroArg       := termParser maxPrec
def macroDollarArg := parser! "$" >> termParser 10
def macroLastArg   := macroDollarArg <|> macroArg

-- Macro for avoiding exponentially big terms when using `STWorld`
@[builtinTermParser] def stateRefT   := parser! "StateRefT" >> macroArg >> macroLastArg

@[builtinTermParser] def dynamicQuot := parser! "`(" >> ident >> "|" >> toggleInsideQuot (parserOfStack 1) >> ")"

end Term

@[builtinTermParser default+1] def Tactic.quot    : Parser := parser! "`(tactic|" >> toggleInsideQuot tacticParser >> ")"
@[builtinTermParser] def Tactic.quotSeq : Parser := parser! "`(tactic|" >> toggleInsideQuot Tactic.seq1 >> ")"

@[builtinTermParser] def Level.quot  : Parser := parser! "`(level|" >> toggleInsideQuot levelParser >> ")"

builtin_initialize
  registerParserAlias! "letDecl"         Term.letDecl
  registerParserAlias! "haveDecl"        Term.haveDecl
  registerParserAlias! "sufficesDecl"    Term.sufficesDecl
  registerParserAlias! "letRecDecls"     Term.letRecDecls
  registerParserAlias! "hole"            Term.hole
  registerParserAlias! "syntheticHole"   Term.syntheticHole
  registerParserAlias! "matchDiscr"      Term.matchDiscr
  registerParserAlias! "bracketedBinder" Term.bracketedBinder
  registerParserAlias! "attrKind"        Term.attrKind

end Parser
end Lean
