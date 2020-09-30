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

def doSeqIndent    := many1Indent $ doElemParser >> optional "; "
def doSeqBracketed := parser! "{" >> sepBy1 doElemParser "; " true >> "}"
def doSeq          := doSeqBracketed <|> doSeqIndent

@[builtinDoElemParser] def doLet  := parser! "let " >> letDecl
def doId   := parser! try (ident >> optType >> leftArrow) >> termParser
def doPat  := parser! try (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
@[builtinDoElemParser] def doLetArrow := parser! "let " >> (doId <|> doPat)
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
  "if " >> termParser >> " then " >> doSeq
  >> many (checkColGe "'else if' in 'do' must be indented" >> try (" else " >> " if ") >> termParser >> " then " >> doSeq)
  >> optional (checkColGe "'else' in 'do' must be indented" >> " else " >> doSeq)
@[builtinDoElemParser] def doUnless := parser! "unless " >> termParser >> "do " >> doSeq
@[builtinDoElemParser] def doFor    := parser! "for " >> termParser >> " in " >> termParser >> "do " >> doSeq
@[builtinDoElemParser] def doTry    := parser! "try " >> doSeq >> optional ("catch " >> binderIdent >> darrow >> doSeq) >> optional ("finally " >> doSeq)

/- `match`-expression where the right-hand-side of alternatives is a `doSeq` instead of a `term` -/
def doMatchAlt : Parser  := sepBy1 termParser ", " >> darrow >> doSeq
def doMatchAlts : Parser := parser! withPosition $ (optional "| ") >> sepBy1 doMatchAlt (checkColGe "alternatives must be indented" >> "|")
@[builtinDoElemParser] def doMatch := parser!:leadPrec "match " >> sepBy1 matchDiscr ", " >> optType >> " with " >> doMatchAlts

@[builtinDoElemParser] def «break»     := parser! "break"
@[builtinDoElemParser] def «continue»  := parser! "continue"
@[builtinDoElemParser] def «return»    := parser!:leadPrec "return " >> termParser
@[builtinDoElemParser] def doDbgTrace  := parser!:leadPrec "dbgTrace! " >> termParser
@[builtinDoElemParser] def doAssert    := parser!:leadPrec "assert! " >> termParser

/-
We use `notFollowedBy` to avoid counterintuitive behavior. For example, the `if`-term parser
doesn't enforce indentation restrictions, but we don't want it to be used when `doIf` fails.
Note that parser priorities would not solve this problem since the `doIf` parser is failing while the `if`
parser is succeeding.
-/
@[builtinDoElemParser] def doExpr   := parser! notFollowedBy ("if" <|> "match" <|> "let" <|> "have" <|> "do") >> termParser

@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> doSeq

end Term
end Parser
end Lean
