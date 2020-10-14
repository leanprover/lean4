/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Basic
import Lean.Parser.Level

namespace Lean
namespace Parser

@[init] def regBuiltinTacticParserAttr : IO Unit :=
let leadingIdentAsSymbol := true;
registerBuiltinParserAttribute `builtinTacticParser `tactic leadingIdentAsSymbol

@[init] def regTacticParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `tacticParser `tactic

@[inline] def tacticParser (rbp : Nat := 0) : Parser :=
categoryParser `tactic rbp

namespace Tactic

def tacticSeq1Indented : Parser :=
parser! many1Indent (group (tacticParser >> optional ";" >> ppLine))
def tacticSeqBracketed : Parser :=
parser! "{" >> many (group (tacticParser >> optional ";" >> ppLine)) >> "}"
def tacticSeq :=
nodeWithAntiquot "tacticSeq" `Lean.Parser.Tactic.tacticSeq $ tacticSeqBracketed <|> tacticSeq1Indented

/- Raw sequence for quotation and grouping -/
def seq1 :=
node `Lean.Parser.Tactic.seq1 $ sepBy1 tacticParser ";\n" true

end Tactic

def darrow : Parser := " => "

namespace Term

/- Helper functions for defining simple parsers -/

def unicodeInfixR (sym : String) (asciiSym : String) (prec : Nat) : TrailingParser :=
checkPrec prec >> unicodeSymbol sym asciiSym >> termParser prec

def infixR (sym : String) (prec : Nat) : TrailingParser :=
checkPrec prec >> symbol sym >> termParser prec

def unicodeInfixL (sym : String) (asciiSym : String) (prec : Nat) : TrailingParser :=
checkPrec prec >> unicodeSymbol sym asciiSym >> termParser (prec+1)

def infixL (sym : String) (prec : Nat) : TrailingParser :=
checkPrec prec >> symbol sym >> termParser (prec+1)

/- Built-in parsers -/

@[builtinTermParser] def byTactic := parser!:leadPrec "by " >> Tactic.tacticSeq

def optSemicolon (p : Parser) : Parser := ppDedent $ optional ";" >> ppLine >> p

-- `checkPrec` necessary for the pretty printer
@[builtinTermParser] def ident := checkPrec maxPrec >> Parser.ident
@[builtinTermParser] def num : Parser := checkPrec maxPrec >> numLit
@[builtinTermParser] def str : Parser := checkPrec maxPrec >> strLit
@[builtinTermParser] def char : Parser := checkPrec maxPrec >> charLit
@[builtinTermParser] def type := parser! "Type" >> optional (checkWsBefore "" >> checkPrec leadPrec >> levelParser maxPrec)
@[builtinTermParser] def sort := parser! "Sort" >> optional (checkWsBefore "" >> checkPrec leadPrec >> levelParser maxPrec)
@[builtinTermParser] def prop := parser! "Prop"
@[builtinTermParser] def hole := parser! "_"
@[builtinTermParser] def syntheticHole := parser! "?" >> (ident <|> hole)
@[builtinTermParser] def «sorry» := parser! "sorry"
@[builtinTermParser] def cdot   := parser! "·"
@[builtinTermParser] def emptyC := parser! "∅" <|> ("{" >> "}")
def typeAscription := parser! " : " >> termParser
def tupleTail      := parser! ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := parser! "(" >> withoutPosition (withoutForbidden (optional (termParser >> parenSpecial))) >> ")"
@[builtinTermParser] def anonymousCtor := parser! "⟨" >> sepBy termParser ", " >> "⟩"
def optIdent : Parser := optional (try (ident >> " : "))
@[builtinTermParser] def «if»  := parser!:leadPrec "if " >> optIdent >> termParser >> " then " >> termParser >> " else " >> termParser
def fromTerm   := parser! " from " >> termParser
def haveAssign := parser! " := " >> termParser
def haveDecl   := optIdent >> termParser >> (haveAssign <|> fromTerm <|> byTactic)
@[builtinTermParser] def «have» := parser!:leadPrec withPosition ("have " >> haveDecl) >> optSemicolon termParser
def sufficesDecl := optIdent >> termParser >> fromTerm
@[builtinTermParser] def «suffices» := parser!:leadPrec withPosition ("suffices " >> sufficesDecl) >> optSemicolon termParser
@[builtinTermParser] def «show»     := parser!:leadPrec "show " >> termParser >> (fromTerm <|> byTactic)
def structInstArrayRef := parser! "[" >> termParser >>"]"
def structInstLVal   := (ident <|> fieldIdx <|> structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := ppGroup $ parser! structInstLVal >> " := " >> termParser
@[builtinTermParser] def structInst := parser! "{" >> ppHardSpace >> optional (try (termParser >> " with ")) >> sepBy structInstField ", " true >> optional ".." >> optional (" : " >> termParser) >> " }"
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def subtype := parser! "{ " >> ident >> optType >> " // " >> termParser >> " }"
@[builtinTermParser] def listLit := parser! "[" >> sepBy termParser "," true >> "]"
@[builtinTermParser] def arrayLit := parser! "#[" >> sepBy termParser "," true >> "]"
@[builtinTermParser] def explicit := parser! "@" >> termParser maxPrec
@[builtinTermParser] def inaccessible := parser! ".(" >> termParser >> ")"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then group (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := parser! try (" := " >> " by ") >> Tactic.tacticSeq
def binderDefault := parser! " := " >> termParser
def explicitBinder (requireType := false) := ppGroup $ parser! "(" >> many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault) >> ")"
def implicitBinder (requireType := false) := ppGroup $ parser! "{" >> many1 binderIdent >> binderType requireType >> "}"
def instBinder := ppGroup $ parser! "[" >> optIdent >> termParser >> "]"
def bracketedBinder (requireType := false) := explicitBinder requireType <|> implicitBinder requireType <|> instBinder

/-
It is feasible to support dependent arrows such as `{α} → α → α` without sacrificing the quality of the error messages for the longer case.
`{α} → α → α` would be short for `{α : Type} → α → α`
Here is the encoding:
```
def implicitShortBinder := node `Lean.Parser.Term.implicitBinder $ "{" >> many1 binderIdent >> pushNone >> "}"
def depArrowShortPrefix := try (implicitShortBinder >> checkPrec 25 >> unicodeSymbol " → " " -> ")
def depArrowLongPrefix  := bracketedBinder true >> checkPrec 25 >> unicodeSymbol " → " " -> "
def depArrowPrefix      := depArrowShortPrefix <|> depArrowLongPrefix
@[builtinTermParser] def depArrow := parser! depArrowPrefix >> termParser
```
Note that no changes in the elaborator are needed.
We decided to not use it because terms such as `{α} → α → α` may look too cryptic.
Note that we did not add a `explicitShortBinder` parser since `(α) → α → α` is really cryptic as a short for `(α : Type) → α → α`.
-/
@[builtinTermParser] def depArrow := parser! bracketedBinder true >> checkPrec 25 >> unicodeSymbol " → " " -> " >> termParser

def simpleBinder := parser! many1 binderIdent
@[builtinTermParser] def «forall» := parser!:leadPrec unicodeSymbol "∀ " "forall" >> many1 (ppSpace >> (simpleBinder <|> bracketedBinder)) >> ", " >> termParser

def matchAlt : Parser :=
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
  sepBy1 termParser ", " >> darrow >> termParser

def matchAlts (optionalFirstBar := true) : Parser :=
parser! ppDedent $ withPosition $
  ppLine >> (if optionalFirstBar then optional "| " else "| ") >>
  sepBy1 (ppIndent matchAlt) (ppLine >> checkColGe "alternatives must be indented" >> "| ")

def matchDiscr := parser! optional (try (ident >> checkNoWsBefore "no space before ':'" >> ":")) >> termParser

@[builtinTermParser] def «match» := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> matchAlts
@[builtinTermParser] def «nomatch»  := parser!:leadPrec "nomatch " >> termParser

def funImplicitBinder := try (lookahead ("{" >> many1 binderIdent >> (" : " <|> "}"))) >> implicitBinder
def funBinder : Parser := funImplicitBinder <|> instBinder <|> termParser maxPrec
@[builtinTermParser] def «fun» := parser!:maxPrec unicodeSymbol "λ" "fun" >> ((many1 (ppSpace >> funBinder) >> darrow >> termParser) <|> matchAlts false)

def optExprPrecedence := optional (try ":" >> termParser maxPrec)
@[builtinTermParser] def «parser!»  := parser!:leadPrec "parser! " >> optExprPrecedence >> termParser
@[builtinTermParser] def «tparser!» := parser!:leadPrec "tparser! " >> optExprPrecedence >> termParser
@[builtinTermParser] def borrowed   := parser! "@&" >> termParser leadPrec
@[builtinTermParser] def quotedName := parser! nameLit
-- NOTE: syntax quotations are defined in Init.Lean.Parser.Command
@[builtinTermParser] def «match_syntax» := parser!:leadPrec "match_syntax" >> termParser >> " with " >> matchAlts

/- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser := ident >> checkWsBefore "expected space before binders" >> many (ppSpace >> bracketedBinder) >> optType
def letIdDecl   := node `Lean.Parser.Term.letIdDecl   $ try (letIdLhs >> " := ") >> termParser
def letPatDecl  := node `Lean.Parser.Term.letPatDecl  $ try (termParser >> pushNone >> optType >> " := ") >> termParser
def letEqnsDecl := node `Lean.Parser.Term.letEqnsDecl $ letIdLhs >> matchAlts false
-- Remark: we use `nodeWithAntiquot` here to make sure anonymous antiquotations (e.g., `$x`) are not `letDecl`
def letDecl     := nodeWithAntiquot "letDecl" `Lean.Parser.Term.letDecl (notFollowedBy (nonReservedSymbol "rec") >> (letIdDecl <|> letPatDecl <|> letEqnsDecl))
@[builtinTermParser] def «let» := parser!:leadPrec  withPosition ("let " >> letDecl) >> optSemicolon termParser
@[builtinTermParser] def «let!» := parser!:leadPrec withPosition ("let! " >> letDecl) >> optSemicolon termParser
@[builtinTermParser] def «let*» := parser!:leadPrec withPosition ("let* " >> letDecl) >> optSemicolon termParser
def attrArg : Parser := ident <|> strLit <|> numLit
-- use `rawIdent` because of attribute names such as `instance`
def attrInstance     := ppGroup $ parser! rawIdent >> many (ppSpace >> attrArg)
def attributes       := parser! "@[" >> sepBy1 attrInstance ", " >> "]"
def letRecDecls      := sepBy1 (group (optional «attributes» >> letDecl)) ", "
@[builtinTermParser] def «letrec» :=
    parser!:leadPrec withPosition (group ("let " >> nonReservedSymbol "rec ") >> letRecDecls) >> optSemicolon termParser

@[builtinTermParser] def nativeRefl   := parser! "nativeRefl! " >> termParser maxPrec
@[builtinTermParser] def nativeDecide := parser! "nativeDecide! " >> termParser maxPrec
@[builtinTermParser] def decide       := parser! "decide! " >> termParser maxPrec

@[builtinTermParser] def typeOf             := parser! "typeOf! " >> termParser maxPrec
@[builtinTermParser] def ensureTypeOf       := parser! "ensureTypeOf! " >> termParser maxPrec >> strLit >> termParser
@[builtinTermParser] def ensureExpectedType := parser! "ensureExpectedType! " >> strLit >> termParser maxPrec

@[builtinTermParser] def not    := parser! "¬" >> termParser 40
@[builtinTermParser] def bnot   := parser! "!" >> termParser 40
-- symbol precedence should be higher, but must match the one of `sub` below
@[builtinTermParser] def uminus := parser!:65 "-" >> termParser 100

def namedArgument  := parser! try ("(" >> ident >> " := ") >> termParser >> ")"
def ellipsis       := parser! ".."
@[builtinTermParser] def app      := tparser!:(maxPrec-1) many1 $
  checkWsBefore "expected space" >>
  checkColGt "expected to be indented" >>
  (namedArgument <|> termParser maxPrec <|> ellipsis)

@[builtinTermParser] def proj     := tparser! checkNoWsBefore >> "." >> (fieldIdx <|> ident)
@[builtinTermParser] def arrayRef := tparser! checkNoWsBefore >> "[" >> termParser >>"]"
@[builtinTermParser] def arrow    := tparser! unicodeInfixR " → " " -> " 25

def isIdent (stx : Syntax) : Bool :=
-- antiquotations should also be allowed where an identifier is expected
stx.isAntiquot || stx.isIdent

-- NOTE: `check*` should be used *before* `tparser!` so that it is also applied to the generated
-- antiquotation.
@[builtinTermParser] def explicitUniv : TrailingParser := checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '.{'" >> tparser! ".{" >> sepBy1 levelParser ", " >> "}"
@[builtinTermParser] def namedPattern : TrailingParser := checkStackTop isIdent "expected preceding identifier" >> checkNoWsBefore "no space before '@'" >> tparser! "@" >> termParser maxPrec

@[builtinTermParser] def dollar     := tparser!:0 try (" $" >> checkWsBefore "expected space") >> termParser 0
@[builtinTermParser] def dollarProj := tparser!:0 " $. " >> (fieldIdx <|> ident)

-- TODO: fix
@[builtinTermParser] def «where»    := tparser!:0 " where " >> sepBy1 letDecl (group (";\n" >> symbol " where "))

@[builtinTermParser] def fcomp  := tparser! infixR " ∘ " 90

@[builtinTermParser] def prod  := tparser! infixR " × " 35

@[builtinTermParser] def add   := tparser! infixL " + "  65
@[builtinTermParser] def sub   := tparser! infixL " - "  65
@[builtinTermParser] def mul   := tparser! infixL " * "  70
@[builtinTermParser] def div   := tparser! infixL " / "  70
@[builtinTermParser] def mod   := tparser! infixL " % "  70
@[builtinTermParser] def modN  := tparser! infixL " %ₙ " 70
@[builtinTermParser] def pow   := tparser! infixR " ^ " 80

@[builtinTermParser] def le    := tparser! unicodeInfixL " ≤ " " <= " 50
@[builtinTermParser] def ge    := tparser! unicodeInfixL " ≥ " " >= " 50
@[builtinTermParser] def lt    := tparser! infixL " < " 50
@[builtinTermParser] def gt    := tparser! infixL " > " 50
@[builtinTermParser] def eq    := tparser! infixL " = " 50
@[builtinTermParser] def ne    := tparser! infixL " ≠ " 50
@[builtinTermParser] def beq   := tparser! infixL " == " 50
@[builtinTermParser] def bne   := tparser! infixL " != " 50
@[builtinTermParser] def heq   := tparser! unicodeInfixL " ≅ " " ~= " 50
@[builtinTermParser] def equiv := tparser! infixL " ≈ " 50

@[builtinTermParser] def subst := tparser!:75 " ▸ " >> sepBy1 (termParser 75) " ▸ "

@[builtinTermParser] def and   := tparser! unicodeInfixR " ∧ " " /\\ " 35
@[builtinTermParser] def or    := tparser! unicodeInfixR " ∨ " " \\/ " 30
@[builtinTermParser] def iff   := tparser! unicodeInfixL " ↔ " " <-> " 20

@[builtinTermParser] def band  := tparser! infixL " && " 35
@[builtinTermParser] def bor   := tparser! infixL " || " 30

@[builtinTermParser] def append := tparser! infixL " ++ " 65
@[builtinTermParser] def cons   := tparser! infixR " :: " 67

@[builtinTermParser] def orelse      := tparser! infixR " <|> " 2
@[builtinTermParser] def orM         := tparser! infixR " <||> " 30
@[builtinTermParser] def andM        := tparser! infixR " <&&> " 35
@[builtinTermParser] def andthen     := tparser! infixR " >> "  60
@[builtinTermParser] def bindOp      := tparser! infixL " >>= " 55
@[builtinTermParser] def mapRev      := tparser! infixR " <&> " 100
@[builtinTermParser] def seq         := tparser! infixL " <*> " 60
@[builtinTermParser] def seqLeft     := tparser! infixL " <* "  60
@[builtinTermParser] def seqRight    := tparser! infixR " *> "  60
@[builtinTermParser] def map         := tparser! infixR " <$> " 100

@[builtinTermParser] def funBinder.quot : Parser := parser! "`(funBinder|"  >> toggleInsideQuot funBinder >> ")"

@[builtinTermParser] def panic       := parser!:leadPrec "panic! " >> termParser
@[builtinTermParser] def unreachable := parser!:leadPrec "unreachable!"
@[builtinTermParser] def dbgTrace    := parser!:leadPrec withPosition ("dbgTrace! " >> ((interpolatedStr termParser) <|> termParser)) >> optSemicolon termParser
@[builtinTermParser] def assert      := parser!:leadPrec withPosition ("assert! " >> termParser) >> optSemicolon termParser

end Term

@[builtinTermParser 1] def Tactic.quot    : Parser := parser! "`(tactic|" >> toggleInsideQuot tacticParser >> ")"
@[builtinTermParser]   def Tactic.quotSeq : Parser := parser! "`(tactic|" >> toggleInsideQuot Tactic.seq1 >> ")"

@[builtinTermParser] def Level.quot  : Parser := parser! "`(level|" >> toggleInsideQuot levelParser >> ")"

end Parser
end Lean
