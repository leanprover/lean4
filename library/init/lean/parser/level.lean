/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Level-level parsers
-/
prelude
import init.lean.parser.pratt

namespace lean
namespace parser
open combinators parser.hasView monadParsec

@[derive monad alternative monadReader monadParsec monadExcept monadRec monadBasicParser]
def levelParserM := recT nat syntax basicParserM
abbrev levelParser := levelParserM syntax

/-- A level parser for a suffix or infix notation that accepts a preceding term level. -/
@[derive monad alternative monadReader monadParsec monadExcept monadRec monadBasicParser]
def trailingLevelParserM := readerT syntax levelParserM
abbrev trailingLevelParser := trailingLevelParserM syntax

instance trailingLevelParserCoe : hasCoe levelParser trailingLevelParser :=
⟨λ x _, x⟩

@[derive parser.hasTokens parser.hasView]
def level.parser (rbp := 0) : levelParser :=
recurse rbp <?> "universe level"

namespace level
/-- Access leading term -/
def getLeading : trailingLevelParser := read
instance : hasTokens getLeading := default _
instance : hasView syntax getLeading := default _

@[derive parser.hasTokens parser.hasView]
def paren.parser : levelParser :=
node! «paren» ["(":maxPrec, inner: level.parser 0, ")"]

@[derive parser.hasTokens parser.hasView]
def leading.parser : levelParser :=
nodeChoice! leading {
  max: symbolOrIdent "max",
  imax: symbolOrIdent "imax",
  hole: symbol "_" maxPrec,
  paren: paren.parser,
  lit: number.parser,
  var: ident.parser
}

@[derive parser.hasTokens parser.hasView]
def app.parser : trailingLevelParser :=
node! app [fn: getLeading, arg: level.parser maxPrec]

@[derive parser.hasTokens parser.hasView]
def addLit.parser : trailingLevelParser :=
node! addLit [lhs: getLeading, "+", rhs: number.parser]

@[derive parser.hasTokens parser.hasView]
def trailing.parser : trailingLevelParser :=
nodeChoice! trailing {
  app: app.parser,
  addLit: addLit.parser
}
end level

@[derive parser.hasTokens parser.hasView]
def levelParser.run (p : levelParser) : basicParser :=
prattParser level.leading.parser level.trailing.parser p

instance levelParserCoe : hasCoe levelParser basicParser :=
⟨levelParser.run⟩

end parser
end lean
