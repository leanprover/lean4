/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Parser.Parser
import Init.Lean.Parser.Level

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

def darrow : Parser := unicodeSymbol "⇒" "=>"

namespace Term

/- Helper functions for defining simple parsers -/

def unicodeInfixR (sym : String) (asciiSym : String) (lbp : Nat) : TrailingParser :=
unicodeSymbol sym asciiSym lbp >> termParser (lbp - 1)

def infixR (sym : String) (lbp : Nat) : TrailingParser :=
symbol sym lbp >> termParser (lbp - 1)

def unicodeInfixL (sym : String) (asciiSym : String) (lbp : Nat) : TrailingParser :=
unicodeSymbol sym asciiSym lbp >> termParser lbp

def infixL (sym : String) (lbp : Nat) : TrailingParser :=
symbol sym lbp >> termParser lbp

def leadPrec := appPrec - 1

/- Built-in parsers -/
-- NOTE: `checkNoWsBefore` should be used *before* `parser!` so that it is also applied to the generated
-- antiquotation.
def explicitUniv := checkNoWsBefore "no space before '.{'" >> parser! ".{" >> sepBy1 levelParser ", " >> "}"
def namedPattern := checkNoWsBefore "no space before '@'" >> parser! "@" >> termParser appPrec
@[builtinTermParser] def id := parser! ident >> optional (explicitUniv <|> namedPattern)
@[builtinTermParser] def num : Parser := parser! numLit
@[builtinTermParser] def str : Parser := parser! strLit
@[builtinTermParser] def char : Parser := parser! charLit
@[builtinTermParser] def type := parser! symbol "Type" appPrec
@[builtinTermParser] def sort := parser! symbol "Sort" appPrec
@[builtinTermParser] def prop := parser! symbol "Prop" appPrec
@[builtinTermParser] def hole := parser! symbol "_" appPrec
@[builtinTermParser] def namedHole := parser! symbol "?" appPrec >> ident
@[builtinTermParser] def «sorry» := parser! symbol "sorry" appPrec
@[builtinTermParser] def cdot   := parser! symbol "·" appPrec
@[builtinTermParser] def emptyC := parser! symbol "∅" appPrec
def typeAscription := parser! " : " >> termParser
def tupleTail      := parser! ", " >> sepBy1 termParser ", "
def parenSpecial : Parser := optional (tupleTail <|> typeAscription)
@[builtinTermParser] def paren := parser! symbol "(" appPrec >> optional (termParser >> parenSpecial) >> ")"
@[builtinTermParser] def anonymousCtor := parser! symbol "⟨" appPrec >> sepBy termParser ", " >> "⟩"
def optIdent : Parser := optional (try (ident >> " : "))
@[builtinTermParser] def «if»  := parser! symbol "if " leadPrec >> optIdent >> termParser >> " then " >> termParser >> " else " >> termParser
def fromTerm   := parser! " from " >> termParser
def haveAssign := parser! " := " >> termParser
@[builtinTermParser] def «have» := parser! symbol "have " leadPrec >> optIdent >> termParser >> (haveAssign <|> fromTerm) >> "; " >> termParser
@[builtinTermParser] def «suffices» := parser! symbol "suffices " leadPrec >> optIdent >> termParser >> fromTerm >> "; " >> termParser
@[builtinTermParser] def «show»     := parser! symbol "show " leadPrec >> termParser >> fromTerm
def structInstArrayRef := parser! "[" >> termParser >>"]"
def structInstLVal   := (ident <|> fieldIdx <|> structInstArrayRef) >> many (group ("." >> (ident <|> fieldIdx)) <|> structInstArrayRef)
def structInstField  := parser! structInstLVal >> " := " >> termParser
def structInstSource := parser! ".." >> optional termParser
@[builtinTermParser] def structInst := parser! symbol "{" appPrec >> optional (try (ident >> checkWsBefore "expected space '.'" >> " . ")) >> sepBy (structInstField <|> structInstSource) ", " true >> "}"
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec
@[builtinTermParser] def subtype := parser! "{" >> ident >> optType >> " // " >> termParser >> "}"
@[builtinTermParser] def listLit := parser! symbol "[" appPrec >> sepBy termParser "," true >> "]"
@[builtinTermParser] def arrayLit := parser! symbol "#[" appPrec >> sepBy termParser "," true >> "]"
@[builtinTermParser] def explicit := parser! symbol "@" appPrec >> termParser appPrec
@[builtinTermParser] def inaccessible := parser! symbol ".(" appPrec >> termParser >> ")"
def binderIdent : Parser  := ident <|> hole
def binderType (requireType := false) : Parser := if requireType then group (" : " >> termParser) else optional (" : " >> termParser)
def binderTactic  := parser! try (" := " >> " by ") >> Tactic.nonEmptySeq
def binderDefault := parser! " := " >> termParser
def explicitBinder (requireType := false) := parser! "(" >> many1 binderIdent >> binderType requireType >> optional (binderTactic <|> binderDefault) >> ")"
def implicitBinder (requireType := false) := parser! "{" >> many1 binderIdent >> binderType requireType >> "}"
def instBinder := parser! "[" >> optIdent >> termParser >> "]"
def bracktedBinder (requireType := false) := explicitBinder requireType <|> implicitBinder requireType <|> instBinder
@[builtinTermParser] def depArrow := parser! bracktedBinder true >> checkRBPGreater 25 "expected parentheses around dependent arrow" >> unicodeSymbol " → " " -> " >> termParser
def simpleBinder := parser! many1 binderIdent
@[builtinTermParser] def «forall» := parser! unicodeSymbol "∀" "forall" leadPrec >> many1 (simpleBinder <|> bracktedBinder) >> ", " >> termParser

def funBinder : Parser := implicitBinder <|> instBinder <|> termParser appPrec
@[builtinTermParser] def «fun» := parser! unicodeSymbol "λ" "fun" leadPrec >> many1 funBinder >> darrow >> termParser

def matchAlt : Parser :=
nodeWithAntiquot "matchAlt" `Lean.Parser.Term.matchAlt $
  sepBy1 termParser ", " >> darrow >> termParser

def matchAlts (optionalFirstBar := true) : Parser :=
withPosition $ fun pos =>
  (if optionalFirstBar then optional "|" else "|") >>
  sepBy1 matchAlt (checkColGe pos.column "alternatives must be indented" >> "|")

@[builtinTermParser] def «match» := parser! symbol "match " leadPrec >> sepBy1 termParser ", " >> optType >> " with " >> matchAlts
@[builtinTermParser] def «nomatch»  := parser! symbol "nomatch " leadPrec >> termParser
@[builtinTermParser] def «parser!»  := parser! symbol "parser! " leadPrec >> termParser
@[builtinTermParser] def «tparser!» := parser! symbol "tparser! " leadPrec >> termParser
@[builtinTermParser] def borrowed   := parser! symbol "@&" appPrec >> termParser (appPrec - 1)
@[builtinTermParser] def quotedName := parser! nameLit
-- NOTE: syntax quotations are defined in Init.Lean.Parser.Command
@[builtinTermParser] def «match_syntax» := parser! symbol "match_syntax" leadPrec >> termParser >> " with " >> matchAlts

/- Remark: we use `checkWsBefore` to ensure `let x[i] := e; b` is not parsed as `let x [i] := e; b` where `[i]` is an `instBinder`. -/
def letIdLhs    : Parser := ident >> checkWsBefore "expected space before binders" >> many bracktedBinder >> optType
def letIdDecl   : Parser := nodeWithAntiquot "letDecl" `Lean.Parser.Term.letDecl $ try (letIdLhs >> " := ") >> termParser
def letPatDecl  : Parser := node `Lean.Parser.Term.letDecl $ try (termParser >> pushNone >> optType >> " := ") >> termParser
def letEqnsDecl : Parser := node `Lean.Parser.Term.letDecl $ letIdLhs >> matchAlts false
def letDecl              := letIdDecl <|> letPatDecl <|> letEqnsDecl
@[builtinTermParser] def «let» := parser! symbol "let " leadPrec >> letDecl >> "; " >> termParser
@[builtinTermParser] def «let!» := parser! symbol "let! " leadPrec >> letDecl >> "; " >> termParser

def leftArrow : Parser := unicodeSymbol " ← " " <- "
def doLet  := parser! "let " >> letDecl
def doId   := parser! try (ident >> optType >> leftArrow) >> termParser
def doPat  := parser! try (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
def doExpr := parser! termParser
def doElem := doLet <|> doId <|> doPat <|> doExpr
def doSeq  := sepBy1 doElem "; "
def bracketedDoSeq := parser! "{" >> doSeq >> "}"
@[builtinTermParser] def liftMethod := parser! leftArrow >> termParser
@[builtinTermParser] def «do»  := parser! symbol "do " leadPrec >> (bracketedDoSeq <|> doSeq)

@[builtinTermParser] def nativeRefl := parser! "nativeRefl! " >> termParser appPrec

@[builtinTermParser] def not    := parser! symbol "¬" appPrec >> termParser 40
@[builtinTermParser] def bnot   := parser! symbol "!" appPrec >> termParser 40
@[builtinTermParser] def uminus := parser! "-" >> termParser 100

def namedArgument  := parser! try ("(" >> ident >> " := ") >> termParser >> ")"
@[builtinTermParser] def app      := tparser! many1 (namedArgument <|> termParser appPrec)

def checkIsSort := checkStackTop (fun stx => stx.isOfKind `Lean.Parser.Term.type || stx.isOfKind `Lean.Parser.Term.sort)
@[builtinTermParser] def sortApp  := tparser! checkIsSort >> levelParser appPrec
@[builtinTermParser] def proj     := tparser! symbolNoWs "." (appPrec+1) >> (fieldIdx <|> ident)
@[builtinTermParser] def arrow    := tparser! unicodeInfixR " → " " -> " 25
@[builtinTermParser] def arrayRef := tparser! symbolNoWs "[" (appPrec+1) >> termParser >>"]"

@[builtinTermParser] def dollar     := tparser! try (dollarSymbol >> checkWsBefore "space expected") >> termParser 0
@[builtinTermParser] def dollarProj := tparser! symbol "$." 1 >> (fieldIdx <|> ident)

@[builtinTermParser] def «where»    := tparser! symbol " where " 1 >> sepBy1 letDecl (group ("; " >> " where "))

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

@[builtinTermParser] def subst := tparser! symbol " ▸ " 75 >> sepBy1 (termParser 75) " ▸ "

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
@[builtinTermParser] def mapConst    := tparser! infixR " <$ "  100
@[builtinTermParser] def mapConstRev := tparser! infixR " $> "  100

@[builtinTermParser] def tacticBlock := parser! symbol "begin " appPrec >> Tactic.seq >> "end"
@[builtinTermParser] def byTactic    := parser! symbol "by " leadPrec >> Tactic.nonEmptySeq
-- Use `unboxSingleton` trick similar to the one used at Command.lean for `Term.stxQuot`
@[builtinTermParser] def tacticStxQuot : Parser := node `Lean.Parser.Term.stxQuot $ symbol "`(tactic|" appPrec >> sepBy1 tacticParser "; " true true >> ")"

end Term
end Parser
end Lean
