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

/-
  Trailing ';'s in indented "do" blocks are quite convenient, but
  we have to use a few hacks to support them.
  We can't simply set `allowTrailingSep` to `true` at the `sepBy1` parser.
  For example, the parser
  ```
  withPosition fun pos =>
    sepBy1 (checkColGe pos.column "do-elements must be indented" >> doElemParser) "; " true
  ```
  doesn't work because we may consume the ";" of another syntactic construct.
  Example:
  ```
  def tst1 (a : Nat) : IO Unit :=
  let f (x : Nat) : IO Unit := do
    IO.println x;
    pure ();  -- it would consume `;` of the let-expression
  f a
  ```
  The following parser also doesn't work
  ```
  withPosition fun pos =>
    sepBy1 doElemParser (try ("; " >> checkColGe pos.column "do-elements must be indented")) true
  ```
  because the next element after the trailing ';' would have to be indented. Otherwise, it would
  fail the `checkColGe` indentation test.
  ```
    if a < 10 then do
      pure a; -- syntax error here
    else
      IO.println "hello"
  ```
  There are two hacks:
  1- We want a trailing `;` in a `do` sequence where the next element is a command.
  ```
  def foo := do
  IO.println "hello";
  IO.println "world";

  def x := 10
  ```
  We considered using just `notFollowedBy commandParser` after `checkColGe`, but it is inconvenient in IDEs
  since we keep getting a "expected term" error while we are typing the next command after the `do` sequence.
  So, we avoid this problem by using `notFollowedByCommandToken` which fails if the next token is
  the beggining of a command.

  2- We use an `optional "; "` after the `sepBy` to consume the trailing `;` when the next element is not indented,
  or it is a `commandParser`. To ensure we are not consuming the `;` of another syntactic element,
  `notFollowedByTermToken >> notFollowedBy (ident <|> numLit <|> strLit <|> charLit <|> nameLit)`
-/
def doSeqIndent :=
withPosition fun pos₁ =>
  sepBy1
    doElemParser
    -- The separator for the indented `do`-block
    ("; "
     -- check indentation
     >> checkColGe pos₁.column "do-elements must be indented"
     >> notFollowedByCommandToken)
  >> optional (try ("; " >> notFollowedByTermToken >> notFollowedBy (ident <|> numLit <|> strLit <|> charLit <|> nameLit)))
def doSeqBracketed := parser! "{" >> sepBy1 doElemParser "; " true >> "}"
def doSeq          := doSeqBracketed <|> doSeqIndent

@[builtinDoElemParser] def doLet  := parser! "let " >> letDecl
def doId   := parser! try (ident >> optType >> leftArrow) >> termParser
def doPat  := parser! try (termParser >> leftArrow) >> termParser >> optional (" | " >> termParser)
@[builtinDoElemParser] def doAssign := notFollowedBy "let " >> (doId <|> doPat)
@[builtinDoElemParser] def doHave   := parser! "have " >> Term.haveDecl
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
@[builtinDoElemParser] def doIf := parser! withPosition fun pos =>
  "if " >> termParser >> " then " >> doSeq
  >> many (checkColGe pos.column "'else if' in 'do' must be indented" >> try (" else " >> " if ") >> termParser >> " then " >> doSeq)
  >> optional (checkColGe pos.column "'else' in 'do' must be indented" >> " else " >> doSeq)
@[builtinDoElemParser] def doFor := parser! "for " >> termParser >> " in " >> termParser maxPrec >> doSeq
@[builtinDoElemParser] def «break» := parser! "break"
@[builtinDoElemParser] def «continue» := parser! "continue"

@[builtinDoElemParser] def doExpr   := parser! notFollowedBy "let " >> notFollowedBy "have " >> termParser

@[builtinTermParser] def «do»  := parser!:maxPrec "do " >> doSeq

end Term
end Parser
end Lean
