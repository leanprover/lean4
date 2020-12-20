/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term

namespace Lean
namespace Parser

builtin_initialize registerBuiltinParserAttribute `builtinDoElemParser `doElem
builtin_initialize registerBuiltinDynamicParserAttribute `doElemParser `doElem

@[inline] def doElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `doElem rbp

namespace Term
def leftArrow : Parser := unicodeSymbol " ← " " <- "
@[builtinTermParser] def liftMethod := parser!:0 leftArrow >> termParser

def doSeqItem      := parser! ppLine >> doElemParser >> optional "; "
def doSeqIndent    := parser! many1Indent doSeqItem
def doSeqBracketed := parser! "{" >> withoutPosition (many1 doSeqItem) >> ppLine >> "}"
def doSeq          := doSeqBracketed <|> doSeqIndent

def termBeforeDo := withForbidden "do" termParser

attribute [runBuiltinParserAttributeHooks] doSeq termBeforeDo

builtin_initialize
  registerParserAlias! "doSeq" doSeq
  registerParserAlias! "termBeforeDo" termBeforeDo

def notFollowedByRedefinedTermToken :=
  notFollowedBy ("if" <|> "match" <|> "let" <|> "have" <|> "do" <|> "dbgTrace!" <|> "assert!" <|> "for" <|> "unless" <|> "return" <|> symbol "try") "token at 'do' element"

@[builtinDoElemParser] def doLet      := parser! "let " >> optional "mut " >> letDecl

@[builtinDoElemParser] def doLetRec   := parser! group ("let " >> nonReservedSymbol "rec ") >> letRecDecls
def doIdDecl   := parser! atomic (ident >> optType >> leftArrow) >> doElemParser
def doPatDecl  := parser! atomic (termParser >> leftArrow) >> doElemParser >> optional (checkColGt >> " | " >> doElemParser)
@[builtinDoElemParser] def doLetArrow      := parser! withPosition ("let " >> optional "mut " >> (doIdDecl <|> doPatDecl))

-- We use `letIdDeclNoBinders` to define `doReassign`.
-- Motivation: we do not reassign functions, and avoid parser conflict
def letIdDeclNoBinders := node `Lean.Parser.Term.letIdDecl $ atomic (ident >> pushNone >> optType >> " := ") >> termParser

@[builtinDoElemParser] def doReassign      := parser! notFollowedByRedefinedTermToken >> (letIdDeclNoBinders <|> letPatDecl)
@[builtinDoElemParser] def doReassignArrow := parser! notFollowedByRedefinedTermToken >> withPosition (doIdDecl <|> doPatDecl)
@[builtinDoElemParser] def doHave     := parser! "have " >> Term.haveDecl
/-
In `do` blocks, we support `if` without an `else`. Thus, we use indentation to prevent examples such as
```
if c_1 then
  if c_2 then
    action_1
else
  action_2
```
from being parsed as
```
if c_1 then {
  if c_2 then {
    action_1
  } else {
    action_2
  }
}
```
We also have special support for `else if` because we don't want to write
```
if c_1 then
  action_1
else if c_2 then
       action_2
     else
       action_3
```
-/
def elseIf := atomic (group (withPosition (" else " >> checkLineEq >> " if ")))
def doIfLet  := parser! "let " >> termParser >> " := " >> termParser
def doIfCond := parser! optIdent >> termParser
@[builtinDoElemParser] def doIf := parser! withPosition $
  "if " >> (doIfLet <|> doIfCond) >> " then " >> doSeq
  >> many (checkColGe "'else if' in 'do' must be indented" >> group (elseIf >> (doIfLet <|> doIfCond) >> " then " >> doSeq))
  >> optional (checkColGe "'else' in 'do' must be indented" >> " else " >> doSeq)
@[builtinDoElemParser] def doUnless := parser! "unless " >> withForbidden "do" termParser >> "do " >> doSeq
def doForDecl := parser! termParser >> " in " >> withForbidden "do" termParser
@[builtinDoElemParser] def doFor    := parser! "for " >> sepBy1 doForDecl ", " >> "do " >> doSeq

def doMatchAlts := matchAlts (rhsParser := doSeq)
@[builtinDoElemParser] def doMatch := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> doMatchAlts

def doCatch      := parser! atomic ("catch " >> binderIdent) >> optional (" : " >> termParser) >> darrow >> doSeq
def doCatchMatch := parser! "catch " >> doMatchAlts
def doFinally    := parser! "finally " >> doSeq
@[builtinDoElemParser] def doTry    := parser! "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally

@[builtinDoElemParser] def doBreak     := parser! "break"
@[builtinDoElemParser] def doContinue  := parser! "continue"
@[builtinDoElemParser] def doReturn    := parser!:leadPrec withPosition ("return " >> optional (checkLineEq >> termParser))
@[builtinDoElemParser] def doDbgTrace  := parser!:leadPrec "dbgTrace! " >> ((interpolatedStr termParser) <|> termParser)
@[builtinDoElemParser] def doAssert    := parser!:leadPrec "assert! " >> termParser

/-
We use `notFollowedBy` to avoid counterintuitive behavior. For example, the `if`-term parser
doesn't enforce indentation restrictions, but we don't want it to be used when `doIf` fails.
Note that parser priorities would not solve this problem since the `doIf` parser is failing while the `if`
parser is succeeding.
-/
@[builtinDoElemParser] def doExpr   := parser! notFollowedByRedefinedTermToken >> termParser
@[builtinDoElemParser] def doNested := parser! "do " >> doSeq

@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> doSeq

@[builtinTermParser] def doElem.quot : Parser := parser! "`(doElem|" >> toggleInsideQuot doElemParser >> ")"

/- macros for using `unless`, `for`, `try`, `return` as terms. They expand into `do unless ...`, `do for ...`, `do try ...`, and `do return ...` -/
@[builtinTermParser] def termUnless := parser! "unless " >> withForbidden "do" termParser >> "do " >> doSeq
@[builtinTermParser] def termFor    := parser! "for " >> sepBy1 doForDecl ", " >> "do " >> doSeq
@[builtinTermParser] def termTry    := parser! "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally
@[builtinTermParser] def termReturn := parser!:leadPrec withPosition ("return " >> optional (checkLineEq >> termParser))

end Term
end Parser
end Lean
