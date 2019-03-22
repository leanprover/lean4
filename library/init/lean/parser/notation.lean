/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Notation parsers
-/
prelude
import init.lean.parser.token

namespace Lean
namespace Parser

open Combinators MonadParsec
open Parser.HasTokens Parser.HasView

local postfix `?`:10000 := optional
local postfix *:10000 := Combinators.many
local postfix +:10000 := Combinators.many1

@[derive Parser.HasTokens Parser.HasView]
def Term.Parser (rbp := 0) : termParser :=
recurse rbp <?> "Term"

set_option class.instance_max_depth 100

namespace «command»
namespace NotationSpec
@[derive Parser.HasTokens Parser.HasView]
def precedenceLit.Parser : termParser :=
nodeChoice! precedenceLit {
  num: number.Parser,
  max: symbolOrIdent "max",
  -- TODO(Sebastian): `precOf`?
}

def precedenceLit.View.toNat : precedenceLit.View → Nat
| (precedenceLit.View.num n) := n.toNat
| (precedenceLit.View.max _) := maxPrec

@[derive Parser.HasTokens Parser.HasView]
def precedenceTerm.Parser : termParser :=
nodeChoice! precedenceTerm {
  lit: precedenceLit.Parser,
  offset: node! precedenceOffset ["(", lit: precedenceLit.Parser,
    op: nodeChoice! precedenceOffsetOp {" + ", " - "},
    offset: number.Parser,
    ")",
  ]
}

def precedenceTerm.View.toNat : precedenceTerm.View → Nat
| (precedenceTerm.View.lit l) := l.toNat
| (precedenceTerm.View.offset o) := match o.op with
  | (precedenceOffsetOp.View.«+» _) := o.lit.toNat.add o.offset.toNat
  | (precedenceOffsetOp.View.«-» _) := o.lit.toNat - o.offset.toNat

@[derive Parser.HasTokens Parser.HasView]
def precedence.Parser : termParser :=
node! «precedence» [":", Term: precedenceTerm.Parser]

@[derive Parser.HasTokens Parser.HasView]
def quotedSymbol.Parser : termParser :=
raw $ takeUntil (= '`')

@[derive Parser.HasTokens Parser.HasView]
def symbolQuote.Parser : termParser :=
node! symbolQuote [
  leftQuote: rawStr "`",
  symbol: quotedSymbol.Parser,
  rightQuote: rawStr "`" true, -- consume trailing ws
  prec: precedence.Parser?]

def unquotedSymbol.Parser : termParser :=
try $ do {
  it ← leftOver,
  stx@(Syntax.atom _) ← monadLift token | error "" (DList.singleton "symbol") it,
  pure stx
} <?> "symbol"

instance unquotedSymbol.tokens : Parser.HasTokens unquotedSymbol.Parser := ⟨[]⟩
instance unquotedSymbol.View : Parser.HasView (Option SyntaxAtom) unquotedSymbol.Parser :=
{ view := λ stx, match stx with
  | Syntax.atom atom := some atom
  | _                := none,
  review := λ a, (Syntax.atom <$> a).getOrElse Syntax.missing }

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive Parser.HasTokens Parser.HasView]
def notationSymbol.Parser : termParser :=
nodeChoice! notationSymbol {
  quoted: symbolQuote.Parser,
  --TODO(Sebastian): decide if we want this in notations
  --unquoted: unquotedSymbol.Parser
}

@[derive Parser.HasTokens Parser.HasView]
def mixfixSymbol.Parser : termParser :=
nodeChoice! mixfixSymbol {
  quoted: symbolQuote.Parser,
  unquoted: unquotedSymbol.Parser
}

@[derive Parser.HasTokens Parser.HasView]
def foldAction.Parser : termParser :=
node! foldAction [
  "(",
  op: anyOf [symbolOrIdent "foldl", symbolOrIdent "foldr"],
  sep: notationSymbol.Parser,
  folder: node! foldActionFolder [
    "(",
    arg1: ident.Parser,
    arg2: ident.Parser,
    ",",
    rhs: Term.Parser,
    ")"
  ],
  init: Term.Parser,
  endTk: notationSymbol.Parser,
  ")"
]

@[derive Parser.HasTokens Parser.HasView]
def action.Parser : termParser :=
node! action [":", kind: nodeChoice! actionKind {
  prec: try precedenceTerm.Parser,
  prev: symbolOrIdent "prev",
  scoped: node! scopedAction [
    try ["(", scoped: symbolOrIdent "scoped"],
    prec: precedence.Parser?,
    id: ident.Parser,
    ", ",
    Term: Term.Parser,
    ")",
  ],
  fold: foldAction.Parser
}]

@[derive Parser.HasTokens Parser.HasView]
def transition.Parser : termParser :=
nodeChoice! transition {
  binder: node! binder [binder: symbolOrIdent "binder", prec: precedence.Parser?],
  binders: node! binders [binders: symbolOrIdent "binders", prec: precedence.Parser?],
  Arg: node! argument [id: ident.Parser, action: action.Parser?]
}

@[derive Parser.HasTokens Parser.HasView]
def rule.Parser : termParser :=
node! rule [symbol: notationSymbol.Parser, transition: transition.Parser?]

end NotationSpec

@[derive Parser.HasTokens Parser.HasView]
def NotationSpec.Parser : termParser :=
node! NotationSpec [prefixArg: ident.Parser?, rules: NotationSpec.rule.Parser*]

@[derive Parser.HasTokens Parser.HasView]
def notation.Parser : termParser :=
node! «notation» [
  try [«local»: (symbol "local ")?, "notation"],
  spec: NotationSpec.Parser, ":=", Term: Term.Parser]

@[derive Parser.HasTokens Parser.HasView]
def reserveNotation.Parser : termParser :=
node! «reserveNotation» [try ["reserve", "notation"], spec: NotationSpec.Parser]

@[derive Parser.HasTokens Parser.HasView]
def mixfix.kind.Parser : termParser :=
nodeChoice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive Parser.HasTokens Parser.HasView]
def mixfix.Parser : termParser :=
node! «mixfix» [
  try [«local»: (symbol "local ")?, kind: mixfix.kind.Parser],
  symbol: NotationSpec.mixfixSymbol.Parser, ":=", Term: Term.Parser]

@[derive Parser.HasTokens Parser.HasView]
def notationLike.Parser : termParser :=
nodeChoice! notationLike {«notation»: notation.Parser, mixfix: mixfix.Parser}

@[derive Parser.HasTokens Parser.HasView]
def reserveMixfix.Parser : termParser :=
node! «reserveMixfix» [
  try ["reserve", kind: mixfix.kind.Parser],
  symbol: NotationSpec.notationSymbol.Parser]

end «command»
end Parser
end Lean
