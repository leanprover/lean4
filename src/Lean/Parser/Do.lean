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
@[builtinTermParser] def liftMethod := leading_parser:minPrec leftArrow >> termParser

def doSeqItem      := leading_parser ppLine >> doElemParser >> optional "; "
def doSeqIndent    := leading_parser many1Indent doSeqItem
def doSeqBracketed := leading_parser "{" >> withoutPosition (many1 doSeqItem) >> ppLine >> "}"
def doSeq          := doSeqBracketed <|> doSeqIndent

def termBeforeDo := withForbidden "do" termParser

attribute [runBuiltinParserAttributeHooks] doSeq termBeforeDo

builtin_initialize
  register_parser_alias doSeq
  register_parser_alias termBeforeDo

def notFollowedByRedefinedTermToken :=
  -- Remark: we don't currently support `open` and `set_option` in `do`-blocks, but we include them in the following list to fix the ambiguity
  -- "open" command following `do`-block. If we don't add `do`, then users would have to indent `do` blocks or use `{ ... }`.
  notFollowedBy ("set_option" <|> "open" <|> "if" <|> "match" <|> "let" <|> "have" <|> "do" <|> "dbg_trace" <|> "assert!" <|> "for" <|> "unless" <|> "return" <|> symbol "try") "token at 'do' element"

@[builtinDoElemParser] def doLet      := leading_parser "let " >> optional "mut " >> letDecl

@[builtinDoElemParser] def doLetRec   := leading_parser group ("let " >> nonReservedSymbol "rec ") >> letRecDecls
def doIdDecl   := leading_parser atomic (ident >> optType >> leftArrow) >> doElemParser
def doPatDecl  := leading_parser atomic (termParser >> leftArrow) >> doElemParser >> optional (checkColGt >> " | " >> doElemParser)
@[builtinDoElemParser] def doLetArrow      := leading_parser withPosition ("let " >> optional "mut " >> (doIdDecl <|> doPatDecl))

-- We use `letIdDeclNoBinders` to define `doReassign`.
-- Motivation: we do not reassign functions, and avoid parser conflict
def letIdDeclNoBinders := node `Lean.Parser.Term.letIdDecl $ atomic (ident >> pushNone >> optType >> " := ") >> termParser

@[builtinDoElemParser] def doReassign      := leading_parser notFollowedByRedefinedTermToken >> (letIdDeclNoBinders <|> letPatDecl)
@[builtinDoElemParser] def doReassignArrow := leading_parser notFollowedByRedefinedTermToken >> withPosition (doIdDecl <|> doPatDecl)
@[builtinDoElemParser] def doHave     := leading_parser "have " >> Term.haveDecl
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
-- ensure `if $e then ...` still binds to `e:term`
def doIfLetPure := leading_parser " := " >> termParser
def doIfLetBind := leading_parser " ← " >> termParser
def doIfLet     := nodeWithAntiquot "doIfLet"     `Lean.Parser.Term.doIfLet       <| "let " >> termParser >> (doIfLetPure <|> doIfLetBind)
def doIfProp    := nodeWithAntiquot "doIfProp"    `Lean.Parser.Term.doIfProp      <| optIdent >> termParser
def doIfCond    := withAntiquot (mkAntiquot "doIfCond" none (anonymous := false)) <| doIfLet <|> doIfProp
@[builtinDoElemParser] def doIf := leading_parser withPosition $
  "if " >> doIfCond >> " then " >> doSeq
  >> many (checkColGe "'else if' in 'do' must be indented" >> group (elseIf >> doIfCond >> " then " >> doSeq))
  >> optional (checkColGe "'else' in 'do' must be indented" >> " else " >> doSeq)
@[builtinDoElemParser] def doUnless := leading_parser "unless " >> withForbidden "do" termParser >> "do " >> doSeq
def doForDecl := leading_parser termParser >> " in " >> withForbidden "do" termParser
@[builtinDoElemParser] def doFor    := leading_parser "for " >> sepBy1 doForDecl ", " >> "do " >> doSeq

def doMatchAlts := matchAlts (rhsParser := doSeq)
@[builtinDoElemParser] def doMatch := leading_parser:leadPrec "match " >> optional Term.generalizingParam >> sepBy1 matchDiscr ", " >> optType >> " with " >> doMatchAlts

def doCatch      := leading_parser atomic ("catch " >> binderIdent) >> optional (" : " >> termParser) >> darrow >> doSeq
def doCatchMatch := leading_parser "catch " >> doMatchAlts
def doFinally    := leading_parser "finally " >> doSeq
@[builtinDoElemParser] def doTry    := leading_parser "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally

@[builtinDoElemParser] def doBreak     := leading_parser "break"
@[builtinDoElemParser] def doContinue  := leading_parser "continue"
@[builtinDoElemParser] def doReturn    := leading_parser:leadPrec withPosition ("return " >> optional (checkLineEq >> termParser))
@[builtinDoElemParser] def doDbgTrace  := leading_parser:leadPrec "dbg_trace " >> ((interpolatedStr termParser) <|> termParser)
@[builtinDoElemParser] def doAssert    := leading_parser:leadPrec "assert! " >> termParser

/-
We use `notFollowedBy` to avoid counterintuitive behavior.

For example, the `if`-term parser
doesn't enforce indentation restrictions, but we don't want it to be used when `doIf` fails.
Note that parser priorities would not solve this problem since the `doIf` parser is failing while the `if`
parser is succeeding. The first `notFollowedBy` prevents this problem.

Consider the `doElem` `x := (a, b⟩` it contains an error since we are using `⟩` instead of `)`. Thus, `doReassign` parser fails.
However, `doExpr` would succeed consuming just `x`, and cryptic error message is generated after that.
The second `notFollowedBy` prevents this problem.
-/
@[builtinDoElemParser] def doExpr   := leading_parser notFollowedByRedefinedTermToken >> termParser >> notFollowedBy (symbol ":=" <|> symbol "←" <|> symbol "<-") "unexpected token after 'expr' in 'do' block"
@[builtinDoElemParser] def doNested := leading_parser "do " >> doSeq

@[builtinTermParser] def «do»  := leading_parser:argPrec "do " >> doSeq

@[builtinTermParser] def doElem.quot : Parser := leading_parser "`(doElem|" >> incQuotDepth doElemParser >> ")"

/- macros for using `unless`, `for`, `try`, `return` as terms. They expand into `do unless ...`, `do for ...`, `do try ...`, and `do return ...` -/
@[builtinTermParser] def termUnless := leading_parser "unless " >> withForbidden "do" termParser >> "do " >> doSeq
@[builtinTermParser] def termFor    := leading_parser "for " >> sepBy1 doForDecl ", " >> "do " >> doSeq
@[builtinTermParser] def termTry    := leading_parser "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally
@[builtinTermParser] def termReturn := leading_parser:leadPrec withPosition ("return " >> optional (checkLineEq >> termParser))

end Term
end Parser
end Lean
