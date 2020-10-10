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

def doSeqIndent    := parser! many1Indent $ group (doElemParser >> optional "; ")
def doSeqBracketed := parser! "{" >> withoutPosition (many1 (group (doElemParser >> optional "; "))) >> "}"
def doSeq          := doSeqBracketed <|> doSeqIndent

def notFollowedByRedefinedTermToken := notFollowedBy ("if" <|> "match" <|> "let" <|> "have" <|> "do" <|> "dbgTrace!" <|> "assert!")

@[builtinDoElemParser] def doLet      := parser! "let " >> letDecl
@[builtinDoElemParser] def doLetRec   := parser! group ("let " >> nonReservedSymbol "rec ") >> letRecDecls
def doIdDecl   := parser! «try» (ident >> optType >> leftArrow) >> doElemParser
def doPatDecl  := parser! «try» (termParser >> leftArrow) >> doElemParser >> optional (" | " >> doElemParser)
@[builtinDoElemParser] def doLetArrow      := parser! "let " >> (doIdDecl <|> doPatDecl)
@[builtinDoElemParser] def doReassign      := parser! notFollowedByRedefinedTermToken >> (letIdDecl <|> letPatDecl)
@[builtinDoElemParser] def doReassignArrow := parser! notFollowedByRedefinedTermToken >> (doIdDecl <|> doPatDecl)
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
@[builtinDoElemParser] def doIf := parser! withPosition $
  "if " >> optIdent >> termParser >> " then " >> doSeq
  >> many (checkColGe "'else if' in 'do' must be indented" >> group («try» (group (" else " >> " if ")) >> optIdent >> termParser >> " then " >> doSeq))
  >> optional (checkColGe "'else' in 'do' must be indented" >> " else " >> doSeq)
@[builtinDoElemParser] def doUnless := parser! "unless " >> withForbidden "do" termParser >> "do " >> doSeq
@[builtinDoElemParser] def doFor    := parser! "for " >> termParser >> " in " >> withForbidden "do" termParser >> "do " >> doSeq

/- `match`-expression where the right-hand-side of alternatives is a `doSeq` instead of a `term` -/
def doMatchAlt : Parser  := parser! sepBy1 termParser ", " >> darrow >> doSeq
def doMatchAlts : Parser := parser! withPosition $ (optional "| ") >> sepBy1 doMatchAlt (checkColGe "alternatives must be indented" >> "| ")
@[builtinDoElemParser] def doMatch := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> doMatchAlts

def doCatch      := parser! «try» ("catch " >> binderIdent) >> optional (" : " >> termParser) >> darrow >> doSeq
def doCatchMatch := parser! "catch " >> doMatchAlts
def doFinally    := parser! "finally " >> doSeq
@[builtinDoElemParser] def doTry    := parser! "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally

@[builtinDoElemParser] def doBreak     := parser! "break"
@[builtinDoElemParser] def doContinue  := parser! "continue"
@[builtinDoElemParser] def doReturn    := parser!:leadPrec "return " >> optional termParser
@[builtinDoElemParser] def doDbgTrace  := parser!:leadPrec "dbgTrace! " >> termParser
@[builtinDoElemParser] def doAssert    := parser!:leadPrec "assert! " >> termParser

/-
We use `notFollowedBy` to avoid counterintuitive behavior. For example, the `if`-term parser
doesn't enforce indentation restrictions, but we don't want it to be used when `doIf` fails.
Note that parser priorities would not solve this problem since the `doIf` parser is failing while the `if`
parser is succeeding.
-/
@[builtinDoElemParser] def doExpr   := parser! notFollowedByRedefinedTermToken >> termParser

@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> doSeq

@[builtinTermParser] def doElem.quot : Parser := parser! "`(doElem|" >> toggleInsideQuot doElemParser >> ")"

end Term
end Parser
end Lean
