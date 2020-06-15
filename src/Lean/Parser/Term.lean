/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Parser.Parser
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

def Tactic.seq : Parser         := node `Lean.Parser.Tactic.seq $ sepBy tacticParser "; " true
def Tactic.nonEmptySeq : Parser := node `Lean.Parser.Tactic.seq $ sepBy1 tacticParser "; " true

def darrow : Parser := "=>"

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

def leadPrec := maxPrec - 1

/- Built-in parsers -/
-- NOTE: `checkNoWsBefore` should be used *before* `parser!` so that it is also applied to the generated
-- antiquotation.
def explicitUniv := checkNoWsBefore "no space before '.{'" >> parser! ".{" >> sepBy1 levelParser ", " >> "}"
def namedPattern := checkNoWsBefore "no space before '@'" >> parser! "@" >> termParser maxPrec
@[builtinTermParser] def id := parser! ident >> optional (explicitUniv <|> namedPattern)
@[builtinTermParser] def num : Parser := parser! numLit
@[builtinTermParser] def str : Parser := parser! strLit
@[builtinTermParser] def char : Parser := parser! charLit
@[builtinTermParser] def type := parser! "Type" >> optional (checkPrec (maxPrec-1) >> levelParser maxPrec)
@[builtinTermParser] def sort := parser! "Sort" >> optional (checkPrec (maxPrec-1) >> levelParser maxPrec)
@[builtinTermParser] def prop := parser! "Prop"
@[builtinTermParser] def hole := parser! "_"
@[builtinTermParser] def namedHole := parser! "?" >> ident
@[builtinTermParser] def «sorry» := parser! "sorry"
@[builtinTermParser] def cdot   := parser! "·"
@[builtinTermParser] def emptyC := parser! "∅"
def typeAscription := parser! " : " >> termParser
def tupleTail      := parser! ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := parser! "(" >> optional (termParser >> parenSpecial) >> ")"
@[builtinTermParser] def anonymousCtor := parser! "⟨" >> sepBy termParser ", " >> "⟩"
def optIdent : Parser := optional (try (ident >> " : "))
@[builtinTermParser] def «if»  := parser!:leadPrec "if " >> optIdent >> termParser >> " then " >> termParser >> " else " >> termParser
def fromTerm   := parser! " from " >> termParser
def haveAssign := parser! " := " >> termParser
@[builtinTermParser] def «have» := parser!:leadPrec "have " >> optIdent >> termParser >> (haveAssign <|> fromTerm) >> "; " >> termParser
@[builtinTermParser] def «suffices» := parser!:leadPrec "suffices " >> optIdent >> termParser >> fromTerm >> "; " >> termParser
@[builtinTermParser] def «show»     := parser!:leadPrec "show " >> termParser >> fromTerm
def structInstArrayRef := parser! "[" >> termParser >>"]"
def structInstLVal   := (ident <|> fieldIdx <|> structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := parser! structInstLVal >> " := " >> termParser
@[builtinTermParser] def structInst := parser! "{" >> optional (try (termParser >> "with")) >> sepBy structInstField ", " true >> optional ".." >> optional (" : " >> termParser) >> "}"
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def subtype := parser! "{" >> ident >> optType >> " // " >> termParser >> "}"
@[builtinTermParser] def listLit := parser! "[" >> sepBy termParser "," true >> "]"
@[builtinTermParser] def arrayLit := parser! "#[" >> sepBy termParser "," true >> "]"
@[builtinTermParser] def explicit := parser! "@" >> termParser maxPrec
@[builtinTermParser] def inaccessible := parser! ".(" >> termParser >> ")"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then group (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := parser! try (" := " >> " by ") >> Tactic.nonEmptySeq
def binderDefault := parser! " := " >> termParser
def explicitBinder (requireType := false) := parser! "(" >> many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault) >> ")"
def implicitBinder (requireType := false) := parser! "{" >> many1 binderIdent >> binderType requireType >> "}"
def instBinder := parser! "[" >> optIdent >> termParser >> "]"
def bracketedBinder (requireType := false) := explicitBinder requireType <|> implicitBinder requireType <|> instBinder
@[builtinTermParser] def depArrow := parser! bracketedBinder true >> checkPrec 25 >> unicodeSymbol " → " " -> " >> termParser
def simpleBinder := parser! many1 binderIdent
@[builtinTermParser] def «forall» := parser!:leadPrec unicodeSymbol "∀" "forall" >> many1 (simpleBinder <|> bracketedBinder) >> ", " >> termParser

def funBinder : Parser := implicitBinder <|> instBinder <|> termParser maxPrec
@[builtinTermParser] def «fun» := parser!:maxPrec unicodeSymbol "λ" "fun" >> many1 funBinder >> darrow >> termParser

def matchAlt : Parser :=
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
  sepBy1 termParser ", " >> darrow >> termParser

def matchAlts (optionalFirstBar := true) : Parser :=
withPosition $ fun pos =>
  (if optionalFirstBar then optional "|" else "|") >>
  sepBy1 matchAlt (checkColGe pos.column "alternatives must be indented" >> "|")

@[builtinTermParser] def «match» := parser!:leadPrec "match " >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermParser] def «nomatch»  := parser!:leadPrec "nomatch " >> termParser
def optExprPrecedence := optional (try ":" >> termParser maxPrec)
@[builtinTermParser] def «parser!»  := parser!:leadPrec "parser! " >> optExprPrecedence >> termParser
@[builtinTermParser] def «tparser!» := parser!:leadPrec "tparser! " >> optExprPrecedence >> termParser
@[builtinTermParser] def borrowed   := parser! "@&" >> termParser (maxPrec - 1)
@[builtinTermParser] def quotedName := parser! nameLit
-- NOTE: syntax quotations are defined in Init.Lean.Parser.Command
@[builtinTermParser] def «match_syntax» := parser!:leadPrec "match_syntax" >> termParser >> " with " >> matchAlts

/- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser := ident >> checkWsBefore "expected space before binders" >> many bracketedBinder >> optType
def letIdDecl   : Parser := nodeWithAntiquot "letDecl" `Lean.Parser.Term.letDecl $ try (letIdLhs >> " := ") >> termParser
def letPatDecl  : Parser := node `Lean.Parser.Term.letDecl $ try (termParser >> pushNone >> optType >> " := ") >> termParser
def letEqnsDecl : Parser := node `Lean.Parser.Term.letDecl $ letIdLhs >> matchAlts false
def letDecl              := letIdDecl <|> letPatDecl <|> letEqnsDecl
@[builtinTermParser] def «let» := parser!:leadPrec "let " >> letDecl >> "; " >> termParser
@[builtinTermParser] def «let!» := parser!:leadPrec "let! " >> letDecl >> "; " >> termParser

def leftArrow : Parser := unicodeSymbol " ← " " <- "
def doLet  := parser! "let ">> letDecl
def doId   := parser! try (ident >> optType >> leftArrow) >> termParser
def doPat  := parser! try (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
def doExpr := parser! termParser
def doElem := doLet <|> doId <|> doPat <|> doExpr
def doSeq  := sepBy1 doElem "; "
def bracketedDoSeq := parser! "{" >> doSeq >> "}"
@[builtinTermParser] def liftMethod := parser!:0 leftArrow >> termParser
@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> (bracketedDoSeq <|> doSeq)

@[builtinTermParser] def nativeRefl   := parser! "nativeRefl! " >> termParser maxPrec
@[builtinTermParser] def nativeDecide := parser! "nativeDecide! " >> termParser maxPrec
@[builtinTermParser] def decide       := parser! "decide! " >> termParser maxPrec

@[builtinTermParser] def not    := parser! "¬" >> termParser 40
@[builtinTermParser] def bnot   := parser! "!" >> termParser 40
-- symbol precedence should be higher, but must match the one of `sub` below
@[builtinTermParser] def uminus := parser!:65 "-" >> termParser 100

def namedArgument  := parser! try ("(" >> ident >> " := ") >> termParser >> ")"
@[builtinTermParser] def app      := tparser!:(maxPrec-1) checkWsBefore "expected space" >> many1 (namedArgument <|> termParser maxPrec)

@[builtinTermParser] def proj     := tparser! symbolNoWs "." >> (fieldIdx <|> ident)
@[builtinTermParser] def arrow    := tparser! unicodeInfixR " → " " -> " 25
@[builtinTermParser] def arrayRef := tparser! symbolNoWs "[" >> termParser >>"]"

@[builtinTermParser] def dollar     := tparser!:0 try (dollarSymbol >> checkWsBefore "expected space") >> termParser 0
@[builtinTermParser] def dollarProj := tparser!:0 "$." >> (fieldIdx <|> ident)

@[builtinTermParser] def «where»    := tparser!:0 " where " >> sepBy1 letDecl (group ("; " >> symbol " where "))

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
@[builtinTermParser] def bindOp      := tparser! infixR " >>= " 55
@[builtinTermParser] def mapRev      := tparser! infixR " <&> " 100
@[builtinTermParser] def seq         := tparser! infixL " <*> " 60
@[builtinTermParser] def seqLeft     := tparser! infixL " <* "  60
@[builtinTermParser] def seqRight    := tparser! infixR " *> "  60
@[builtinTermParser] def map         := tparser! infixR " <$> " 100

@[builtinTermParser] def tacticBlock := parser! "begin " >> Tactic.seq >> "end"
@[builtinTermParser] def byTactic    := parser!:leadPrec "by " >> Tactic.nonEmptySeq
-- Use `unboxSingleton` trick similar to the one used at Command.lean for `Term.stxQuot`
@[builtinTermParser] def tacticStxQuot    : Parser :=
checkPrec maxPrec >> (node `Lean.Parser.Term.stxQuot $ "`(tactic|" >> sepBy1 tacticParser "; " true true >> ")")
@[builtinTermParser] def levelStxQuot     : Parser :=
checkPrec maxPrec >> (node `Lean.Parser.Term.stxQuot $ "`(level|" >> levelParser >> ")")
@[builtinTermParser] def funBinderStxQuot : Parser :=
checkPrec maxPrec >> (node `Lean.Parser.Term.stxQuot $ "`(funBinder|"  >> funBinder >> ")")

end Term
end Parser
end Lean
