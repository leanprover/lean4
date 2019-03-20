/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Level-Level parsers
-/
prelude
import init.lean.parser.pratt

namespace Lean
namespace Parser
open Combinators Parser.HasView MonadParsec

@[derive Monad Alternative MonadReader MonadParsec MonadExcept MonadRec monadBasicParser]
def LevelParserM := RecT Nat Syntax BasicParserM
abbrev levelParser := LevelParserM Syntax

/-- A Level Parser for a suffix or infix notation that accepts a preceding Term Level. -/
@[derive Monad Alternative MonadReader MonadParsec MonadExcept MonadRec monadBasicParser]
def TrailingLevelParserM := ReaderT Syntax LevelParserM
abbrev trailingLevelParser := TrailingLevelParserM Syntax

instance trailingLevelParserCoe : HasCoe levelParser trailingLevelParser :=
⟨λ x _, x⟩

@[derive Parser.HasTokens Parser.HasView]
def Level.Parser (rbp := 0) : levelParser :=
recurse rbp <?> "universe Level"

namespace Level
/-- Access leading Term -/
def getLeading : trailingLevelParser := read
instance : HasTokens getLeading := default _
instance : HasView Syntax getLeading := default _

@[derive Parser.HasTokens Parser.HasView]
def paren.Parser : levelParser :=
node! «paren» ["(":maxPrec, inner: Level.Parser 0, ")"]

@[derive Parser.HasTokens Parser.HasView]
def leading.Parser : levelParser :=
nodeChoice! leading {
  max: symbolOrIdent "max",
  imax: symbolOrIdent "imax",
  hole: symbol "_" maxPrec,
  paren: paren.Parser,
  lit: number.Parser,
  var: ident.Parser
}

@[derive Parser.HasTokens Parser.HasView]
def app.Parser : trailingLevelParser :=
node! app [fn: getLeading, Arg: Level.Parser maxPrec]

@[derive Parser.HasTokens Parser.HasView]
def addLit.Parser : trailingLevelParser :=
node! addLit [lhs: getLeading, "+", rhs: number.Parser]

@[derive Parser.HasTokens Parser.HasView]
def trailing.Parser : trailingLevelParser :=
nodeChoice! trailing {
  app: app.Parser,
  addLit: addLit.Parser
}
end Level

@[derive Parser.HasTokens Parser.HasView]
def levelParser.run (p : levelParser) : basicParser :=
prattParser Level.leading.Parser Level.trailing.Parser p

instance levelParserCoe : HasCoe levelParser basicParser :=
⟨levelParser.run⟩

end Parser
end Lean
