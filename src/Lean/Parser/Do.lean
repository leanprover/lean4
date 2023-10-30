/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Term

namespace Lean
namespace Parser

builtin_initialize registerBuiltinParserAttribute `builtin_doElem_parser ``Category.doElem
builtin_initialize registerBuiltinDynamicParserAttribute `doElem_parser `doElem

@[inline] def doElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `doElem rbp

namespace Term
def leftArrow : Parser := unicodeSymbol "← " "<- "
@[builtin_term_parser] def liftMethod := leading_parser:minPrec
  leftArrow >> termParser

def doSeqItem      := leading_parser
  ppLine >> doElemParser >> optional "; "
def doSeqIndent    := leading_parser
  many1Indent doSeqItem
def doSeqBracketed := leading_parser
  "{" >> withoutPosition (many1 doSeqItem) >> ppLine >> "}"
/-- A `doSeq` is a sequence of `doElem`, the main argument after the `do` keyword and other
do elements that take blocks. It can either have the form `"{" (doElem ";"?)* "}"` or
`many1Indent (doElem ";"?)`, where `many1Indent` ensures that all the items are at
the same or higher indentation level as the first line. -/
def doSeq          :=
  withAntiquot (mkAntiquot "doSeq" decl_name% (isPseudoKind := true)) <|
    doSeqBracketed <|> doSeqIndent
/-- `termBeforeDo` is defined as `withForbidden("do", term)`, which will parse a term but
disallows `do` outside of a bracketing construct. This is used for parsers like `for _ in t do ...`
or `unless t do ...`, where we do not want `t do ...` to be parsed as an application of `t` to a
`do` block, which would otherwise be allowed. -/
def termBeforeDo := withForbidden "do" termParser

attribute [run_builtin_parser_attribute_hooks] doSeq termBeforeDo

builtin_initialize
  register_parser_alias doSeq
  register_parser_alias termBeforeDo

def notFollowedByRedefinedTermToken :=
  -- Remark: we don't currently support `open` and `set_option` in `do`-blocks,
  -- but we include them in the following list to fix the ambiguity where
  -- an "open" command follows the `do`-block.
  -- If we don't add `do`, then users would have to indent `do` blocks or use `{ ... }`.
  notFollowedBy ("set_option" <|> "open" <|> "if" <|> "match" <|> "let" <|> "have" <|>
      "do" <|> "dbg_trace" <|> "assert!" <|> "for" <|> "unless" <|> "return" <|> symbol "try")
    "token at 'do' element"

@[builtin_doElem_parser] def doLet      := leading_parser
  "let " >> optional "mut " >> letDecl
@[builtin_doElem_parser] def doLetElse  := leading_parser
  "let " >> optional "mut " >> termParser >> " := " >> termParser >>
  checkColGt >> " | " >> doSeq

@[builtin_doElem_parser] def doLetRec   := leading_parser
  group ("let " >> nonReservedSymbol "rec ") >> letRecDecls
def doIdDecl   := leading_parser
  atomic (ident >> optType >> ppSpace >> leftArrow) >>
  doElemParser
def doPatDecl  := leading_parser
  atomic (termParser >> ppSpace >> leftArrow) >>
  doElemParser >> optional (checkColGt >> " | " >> doSeq)
@[builtin_doElem_parser] def doLetArrow      := leading_parser
  withPosition ("let " >> optional "mut " >> (doIdDecl <|> doPatDecl))

-- We use `letIdDeclNoBinders` to define `doReassign`.
-- Motivation: we do not reassign functions, and avoid parser conflict
def letIdDeclNoBinders := node ``letIdDecl <|
  atomic (ident >> pushNone >> optType >> " := ") >> termParser

@[builtin_doElem_parser] def doReassign      := leading_parser
  notFollowedByRedefinedTermToken >> (letIdDeclNoBinders <|> letPatDecl)
@[builtin_doElem_parser] def doReassignArrow := leading_parser
  notFollowedByRedefinedTermToken >> (doIdDecl <|> doPatDecl)
@[builtin_doElem_parser] def doHave     := leading_parser
  "have" >> Term.haveDecl
/-
In `do` blocks, we support `if` without an `else`.
Thus, we use indentation to prevent examples such as
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
def elseIf := atomic (group (withPosition ("else " >> checkLineEq >> " if ")))
-- ensure `if $e then ...` still binds to `e:term`
def doIfLetPure := leading_parser " := " >> termParser
def doIfLetBind := leading_parser " ← " >> termParser
def doIfLet     := leading_parser (withAnonymousAntiquot := false)
  "let " >> termParser >> (doIfLetPure <|> doIfLetBind)
def doIfProp    := leading_parser (withAnonymousAntiquot := false)
  optIdent >> termParser
def doIfCond    :=
  withAntiquot (mkAntiquot "doIfCond" decl_name% (anonymous := false) (isPseudoKind := true)) <|
    doIfLet <|> doIfProp
-- must reset cache as `withPositionAfterLinebreak` will look at syntax not produced by this parser (or even
-- current category call)
@[builtin_doElem_parser] def doIf := leading_parser withResetCache <| withPositionAfterLinebreak <| ppRealGroup <|
  ppRealFill (ppIndent ("if " >> doIfCond >> " then") >> ppSpace >> doSeq) >>
  many (checkColGe "'else if' in 'do' must be indented" >>
    group (ppDedent ppSpace >> ppRealFill (elseIf >> doIfCond >> " then " >> doSeq))) >>
  optional (checkColGe "'else' in 'do' must be indented" >>
    ppDedent ppSpace >> ppRealFill ("else " >> doSeq))
@[builtin_doElem_parser] def doUnless := leading_parser
  "unless " >> withForbidden "do" termParser >> " do " >> doSeq
def doForDecl := leading_parser
  optional (atomic (ident >> " : ")) >> termParser >> " in " >> withForbidden "do" termParser
/--
`for x in e do s`  iterates over `e` assuming `e`'s type has an instance of the `ForIn` typeclass.
`break` and `continue` are supported inside `for` loops.
`for x in e, x2 in e2, ... do s` iterates of the given collections in parallel,
until at least one of them is exhausted.
The types of `e2` etc. must implement the `ToStream` typeclass.
-/
@[builtin_doElem_parser] def doFor    := leading_parser
  "for " >> sepBy1 doForDecl ", " >> "do " >> doSeq

def doMatchAlts := ppDedent <| matchAlts (rhsParser := doSeq)
@[builtin_doElem_parser] def doMatch := leading_parser:leadPrec
  "match " >> optional Term.generalizingParam >> optional Term.motive >>
  sepBy1 matchDiscr ", " >> " with" >> doMatchAlts

def doCatch      := leading_parser
  ppDedent ppLine >> atomic ("catch " >> binderIdent) >> optional (" : " >> termParser) >> darrow >> doSeq
def doCatchMatch := leading_parser
  ppDedent ppLine >> "catch " >> doMatchAlts
def doFinally    := leading_parser
  ppDedent ppLine >> "finally " >> doSeq
@[builtin_doElem_parser] def doTry    := leading_parser
  "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally

/-- `break` exits the surrounding `for` loop. -/
@[builtin_doElem_parser] def doBreak     := leading_parser "break"
/-- `continue` skips to the next iteration of the surrounding `for` loop. -/
@[builtin_doElem_parser] def doContinue  := leading_parser "continue"
/--
`return e` inside of a `do` block makes the surrounding block evaluate to `pure e`,
skipping any further statements.
Note that uses of the `do` keyword in other syntax like in `for _ in _ do`
do not constitute a surrounding block in this sense;
in supported editors, the corresponding `do` keyword of the surrounding block
is highlighted when hovering over `return`.

`return` not followed by a term starting on the same line is equivalent to `return ()`.
-/
@[builtin_doElem_parser] def doReturn    := leading_parser:leadPrec
  withPosition ("return" >> optional (ppSpace >> checkLineEq >> termParser))
/--
`dbg_trace e` prints `e` (which can be an interpolated string literal) to stderr.
It should only be used for debugging.
-/
@[builtin_doElem_parser] def doDbgTrace  := leading_parser:leadPrec
  "dbg_trace " >> ((interpolatedStr termParser) <|> termParser)
/--
`assert! cond` panics if `cond` evaluates to `false`.
-/
@[builtin_doElem_parser] def doAssert    := leading_parser:leadPrec
  "assert! " >> termParser

/-
We use `notFollowedBy` to avoid counterintuitive behavior.

For example, the `if`-term parser doesn't enforce indentation restrictions,
but we don't want it to be used when `doIf` fails.
Note that parser priorities would not solve this problem
since the `doIf` parser is failing while the `if` parser is succeeding.
The first `notFollowedBy` prevents this problem.

Consider the `doElem` `x := (a, b⟩`.
It contains an error since we are using `⟩` instead of `)`.
Thus, `doReassign` parser fails.
However, `doExpr` would succeed consuming just `x`,
and cryptic error message is generated after that.
The second `notFollowedBy` prevents this problem.
-/
@[builtin_doElem_parser] def doExpr   := leading_parser
  notFollowedByRedefinedTermToken >> termParser >>
  notFollowedBy (symbol ":=" <|> symbol "←" <|> symbol "<-")
    "unexpected token after 'expr' in 'do' block"
@[builtin_doElem_parser] def doNested := leading_parser
  "do " >> doSeq

@[builtin_term_parser] def «do»  := leading_parser:argPrec
  ppAllowUngrouped >> "do " >> doSeq

/-
macros for using `unless`, `for`, `try`, `return` as terms.
They expand into `do unless ...`, `do for ...`, `do try ...`, and `do return ...`
-/

/-- `unless e do s` is a nicer way to write `if !e do s`. -/
@[builtin_term_parser] def termUnless := leading_parser
  "unless " >> withForbidden "do" termParser >> " do " >> doSeq
@[builtin_term_parser] def termFor := leading_parser
  "for " >> sepBy1 doForDecl ", " >> " do " >> doSeq
@[builtin_term_parser] def termTry    := leading_parser
  "try " >> doSeq >> many (doCatch <|> doCatchMatch) >> optional doFinally
/--
`return` used outside of `do` blocks creates an implicit block around it
and thus is equivalent to `pure e`, but helps with avoiding parentheses.
-/
@[builtin_term_parser] def termReturn := leading_parser:leadPrec
  withPosition ("return" >> optional (ppSpace >> checkLineEq >> termParser))

end Term
end Parser
end Lean
