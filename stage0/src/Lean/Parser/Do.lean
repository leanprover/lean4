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
@[builtinTermParser] def liftMethod := parser!:0 leftArrow >> termParser

def doSeqIndent    := withPosition fun pos => sepBy1 doElemParser (try ("; " >> checkColGe pos.column "do-elements must be indented"))
def doSeqBracketed := parser! "{" >> sepBy1 doElemParser "; " true >> "}"
def doSeq          := doSeqBracketed <|> doSeqIndent

@[builtinDoElemParser] def doLet  := parser! "let " >> letDecl
def doId   := parser! try (ident >> optType >> leftArrow) >> termParser
def doPat  := parser! try (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
@[builtinDoElemParser] def doAssign := notFollowedBy "let " >> (doId <|> doPat)
@[builtinDoElemParser] def doHave   := parser! "have " >> Term.haveDecl
@[builtinDoElemParser] def doExpr   := parser! notFollowedBy "let " >> notFollowedBy "have " >> termParser

@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> doSeq

end Term
end Parser
end Lean
