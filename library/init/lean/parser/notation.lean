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

open combinators monad_parsec
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

@[derive parser.has_tokens parser.has_view]
def term.parser (rbp := 0) : term_parser :=
recurse rbp <?> "term"

set_option class.instance_max_depth 100

namespace «command»
namespace notation_spec
@[derive parser.has_tokens parser.has_view]
def precedence_lit.parser : term_parser :=
node_choice! precedence_lit {
  num: number.parser,
  max: symbol_or_ident "max",
  -- TODO(Sebastian): `prec_of`?
}

def precedence_lit.view.to_nat : precedence_lit.view → nat
| (precedence_lit.view.num n) := n.to_nat
| (precedence_lit.view.max _) := max_prec

@[derive parser.has_tokens parser.has_view]
def precedence_term.parser : term_parser :=
node_choice! precedence_term {
  lit: precedence_lit.parser,
  offset: node! precedence_offset ["(", lit: precedence_lit.parser,
    op: node_choice! precedence_offset_op {" + ", " - "},
    offset: number.parser,
    ")",
  ]
}

def precedence_term.view.to_nat : precedence_term.view → nat
| (precedence_term.view.lit l) := l.to_nat
| (precedence_term.view.offset o) := match o.op with
  | (precedence_offset_op.view.«+» _) := o.lit.to_nat.add o.offset.to_nat
  | (precedence_offset_op.view.«-» _) := o.lit.to_nat - o.offset.to_nat

@[derive parser.has_tokens parser.has_view]
def precedence.parser : term_parser :=
node! «precedence» [":", term: precedence_term.parser]

@[derive parser.has_tokens parser.has_view]
def quoted_symbol.parser : term_parser :=
raw $ take_until (= '`')

@[derive parser.has_tokens parser.has_view]
def symbol_quote.parser : term_parser :=
node! notation_quoted_symbol [
  left_quote: raw_str "`",
  symbol: quoted_symbol.parser,
  right_quote: raw_str "`" tt, -- consume trailing ws
  prec: precedence.parser?]

def unquoted_symbol.parser : term_parser :=
try $ do {
  it ← left_over,
  stx@(syntax.atom _) ← monad_lift token | error "" (dlist.singleton "symbol") it,
  pure stx
} <?> "symbol"

instance unquoted_symbol.tokens : parser.has_tokens unquoted_symbol.parser := ⟨[]⟩
instance unquoted_symbol.view : parser.has_view (option syntax_atom) unquoted_symbol.parser :=
{ view := λ stx, match stx with
  | syntax.atom atom := some atom
  | _                := none,
  review := λ a, (syntax.atom <$> a).get_or_else syntax.missing }

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive parser.has_tokens parser.has_view]
def notation_symbol.parser : term_parser :=
node_choice! notation_symbol {
  quoted: symbol_quote.parser,
  --TODO(Sebastian): decide if we want this in notations
  --unquoted: unquoted_symbol.parser
}

@[derive parser.has_tokens parser.has_view]
def mixfix_symbol.parser : term_parser :=
node_choice! mixfix_symbol {
  quoted: symbol_quote.parser,
  unquoted: unquoted_symbol.parser
}

@[derive parser.has_tokens parser.has_view]
def fold_action.parser : term_parser :=
node! fold_action [
  "(",
  op: any_of [symbol_or_ident "foldl", symbol_or_ident "foldr"],
  sep: notation_symbol.parser,
  folder: node! fold_action_folder [
    "(",
    arg1: ident.parser,
    arg2: ident.parser,
    ",",
    rhs: term.parser,
    ")"
  ],
  init: term.parser,
  end_tk: notation_symbol.parser,
  ")"
]

@[derive parser.has_tokens parser.has_view]
def action.parser : term_parser :=
node! action [":", kind: node_choice! action_kind {
  prec: try precedence_term.parser,
  prev: symbol_or_ident "prev",
  scoped: node! scoped_action [
    try ["(", scoped: symbol_or_ident "scoped"],
    prec: precedence.parser?,
    id: ident.parser,
    ", ",
    term: term.parser,
    ")",
  ],
  fold: fold_action.parser
}]

@[derive parser.has_tokens parser.has_view]
def transition.parser : term_parser :=
node_choice! transition {
  binder: node! binder [binder: symbol_or_ident "binder", prec: precedence.parser?],
  binders: node! binders [binders: symbol_or_ident "binders", prec: precedence.parser?],
  arg: node! argument [id: ident.parser, action: action.parser?]
}

@[derive parser.has_tokens parser.has_view]
def rule.parser : term_parser :=
node! rule [symbol: notation_symbol.parser, transition: transition.parser?]

end notation_spec

@[derive parser.has_tokens parser.has_view]
def notation_spec.parser : term_parser :=
node! notation_spec [prefix_arg: ident.parser?, rules: notation_spec.rule.parser*]

@[derive parser.has_tokens parser.has_view]
def notation.parser : term_parser :=
node! «notation» [
  try [«local»: (symbol "local ")?, "notation"],
  spec: notation_spec.parser, ":=", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def reserve_notation.parser : term_parser :=
node! «reserve_notation» [try ["reserve", "notation"], spec: notation_spec.parser]

@[derive parser.has_tokens parser.has_view]
def mixfix.kind.parser : term_parser :=
node_choice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive parser.has_tokens parser.has_view]
def mixfix.parser : term_parser :=
node! «mixfix» [
  try [«local»: (symbol "local ")?, kind: mixfix.kind.parser],
  symbol: notation_spec.mixfix_symbol.parser, ":=", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def notation_like.parser : term_parser :=
node_choice! notation_like {«notation»: notation.parser, mixfix: mixfix.parser}

@[derive parser.has_tokens parser.has_view]
def reserve_mixfix.parser : term_parser :=
node! «reserve_mixfix» [
  try ["reserve", kind: mixfix.kind.parser],
  symbol: notation_spec.notation_symbol.parser]

end «command»
end parser
end lean
