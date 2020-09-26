/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term

namespace Lean
namespace Parser

@[init] def regBuiltinDoElemParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinDoElemParser `doElem

@[init] def regDoElemParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `doElemParser `doElem

@[inline] def doElemParser (rbp : Nat := 0) : Parser :=
categoryParser `doElem rbp

namespace Term

def leftArrow : Parser := unicodeSymbol " ← " " <- "
def doLet  := parser! "let ">> letDecl
def doId   := parser! try (ident >> optType >> leftArrow) >> termParser
def doPat  := parser! try (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
def doExpr := parser! termParser
def doHave := parser! "have " >> Term.haveDecl

def doElem := doLet <|> doId <|> doPat <|> doExpr
def doSeq  := withPosition fun pos => sepBy1 doElem (try ("; " >> checkColGe pos.column "do-elements must be indented"))
def bracketedDoSeq := parser! "{" >> sepBy1 doElem "; " >> "}"

@[builtinTermParser] def liftMethod := parser!:0 leftArrow >> termParser
@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> (bracketedDoSeq <|> doSeq)

end Term
end Parser
end Lean
