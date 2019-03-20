/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Notation parsers
-/
prelude
import init.lean.parser.token

namespace lean
namespace parser

open combinators monadParsec
open parser.hasTokens parser.hasView

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

@[derive parser.hasTokens parser.hasView]
def term.parser (rbp := 0) : termParser :=
recurse rbp <?> "term"

setOption class.instanceMaxDepth 100

namespace «command»
namespace notationSpec
@[derive parser.hasTokens parser.hasView]
def precedenceLit.parser : termParser :=
nodeChoice! precedenceLit {
  num: number.parser,
  max: symbolOrIdent "max",
  -- TODO(Sebastian): `precOf`?
}

def precedenceLit.view.toNat : precedenceLit.view → nat
| (precedenceLit.view.num n) := n.toNat
| (precedenceLit.view.max _) := maxPrec

@[derive parser.hasTokens parser.hasView]
def precedenceTerm.parser : termParser :=
nodeChoice! precedenceTerm {
  lit: precedenceLit.parser,
  offset: node! precedenceOffset ["(", lit: precedenceLit.parser,
    op: nodeChoice! precedenceOffsetOp {" + ", " - "},
    offset: number.parser,
    ")",
  ]
}

def precedenceTerm.view.toNat : precedenceTerm.view → nat
| (precedenceTerm.view.lit l) := l.toNat
| (precedenceTerm.view.offset o) := match o.op with
  | (precedenceOffsetOp.view.«+» _) := o.lit.toNat.add o.offset.toNat
  | (precedenceOffsetOp.view.«-» _) := o.lit.toNat - o.offset.toNat

@[derive parser.hasTokens parser.hasView]
def precedence.parser : termParser :=
node! «precedence» [":", term: precedenceTerm.parser]

@[derive parser.hasTokens parser.hasView]
def quotedSymbol.parser : termParser :=
raw $ takeUntil (= '`')

@[derive parser.hasTokens parser.hasView]
def symbolQuote.parser : termParser :=
node! symbolQuote [
  leftQuote: rawStr "`",
  symbol: quotedSymbol.parser,
  rightQuote: rawStr "`" tt, -- consume trailing ws
  prec: precedence.parser?]

def unquotedSymbol.parser : termParser :=
try $ do {
  it ← leftOver,
  stx@(syntax.atom _) ← monadLift token | error "" (dlist.singleton "symbol") it,
  pure stx
} <?> "symbol"

instance unquotedSymbol.tokens : parser.hasTokens unquotedSymbol.parser := ⟨[]⟩
instance unquotedSymbol.view : parser.hasView (option syntaxAtom) unquotedSymbol.parser :=
{ view := λ stx, match stx with
  | syntax.atom atom := some atom
  | _                := none,
  review := λ a, (syntax.atom <$> a).getOrElse syntax.missing }

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive parser.hasTokens parser.hasView]
def notationSymbol.parser : termParser :=
nodeChoice! notationSymbol {
  quoted: symbolQuote.parser,
  --TODO(Sebastian): decide if we want this in notations
  --unquoted: unquotedSymbol.parser
}

@[derive parser.hasTokens parser.hasView]
def mixfixSymbol.parser : termParser :=
nodeChoice! mixfixSymbol {
  quoted: symbolQuote.parser,
  unquoted: unquotedSymbol.parser
}

@[derive parser.hasTokens parser.hasView]
def foldAction.parser : termParser :=
node! foldAction [
  "(",
  op: anyOf [symbolOrIdent "foldl", symbolOrIdent "foldr"],
  sep: notationSymbol.parser,
  folder: node! foldActionFolder [
    "(",
    arg1: ident.parser,
    arg2: ident.parser,
    ",",
    rhs: term.parser,
    ")"
  ],
  init: term.parser,
  endTk: notationSymbol.parser,
  ")"
]

@[derive parser.hasTokens parser.hasView]
def action.parser : termParser :=
node! action [":", kind: nodeChoice! actionKind {
  prec: try precedenceTerm.parser,
  prev: symbolOrIdent "prev",
  scoped: node! scopedAction [
    try ["(", scoped: symbolOrIdent "scoped"],
    prec: precedence.parser?,
    id: ident.parser,
    ", ",
    term: term.parser,
    ")",
  ],
  fold: foldAction.parser
}]

@[derive parser.hasTokens parser.hasView]
def transition.parser : termParser :=
nodeChoice! transition {
  binder: node! binder [binder: symbolOrIdent "binder", prec: precedence.parser?],
  binders: node! binders [binders: symbolOrIdent "binders", prec: precedence.parser?],
  arg: node! argument [id: ident.parser, action: action.parser?]
}

@[derive parser.hasTokens parser.hasView]
def rule.parser : termParser :=
node! rule [symbol: notationSymbol.parser, transition: transition.parser?]

end notationSpec

@[derive parser.hasTokens parser.hasView]
def notationSpec.parser : termParser :=
node! notationSpec [prefixArg: ident.parser?, rules: notationSpec.rule.parser*]

@[derive parser.hasTokens parser.hasView]
def notation.parser : termParser :=
node! «notation» [
  try [«local»: (symbol "local ")?, "notation"],
  spec: notationSpec.parser, ":=", term: term.parser]

@[derive parser.hasTokens parser.hasView]
def reserveNotation.parser : termParser :=
node! «reserveNotation» [try ["reserve", "notation"], spec: notationSpec.parser]

@[derive parser.hasTokens parser.hasView]
def mixfix.kind.parser : termParser :=
nodeChoice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive parser.hasTokens parser.hasView]
def mixfix.parser : termParser :=
node! «mixfix» [
  try [«local»: (symbol "local ")?, kind: mixfix.kind.parser],
  symbol: notationSpec.mixfixSymbol.parser, ":=", term: term.parser]

@[derive parser.hasTokens parser.hasView]
def notationLike.parser : termParser :=
nodeChoice! notationLike {«notation»: notation.parser, mixfix: mixfix.parser}

@[derive parser.hasTokens parser.hasView]
def reserveMixfix.parser : termParser :=
node! «reserveMixfix» [
  try ["reserve", kind: mixfix.kind.parser],
  symbol: notationSpec.notationSymbol.parser]

end «command»
end parser
end lean
