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
namespace «command»

open combinators monad_parsec
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

set_option class.instance_max_depth 100

namespace notation_spec
@[derive parser.has_tokens parser.has_view]
def precedence.parser : term_parser :=
node! «precedence» [":", prec: number]/-TODO <|> expr-/

def quoted_symbol.parser : term_parser :=
do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, s⟩

instance quoted_symbol.tokens : parser.has_tokens quoted_symbol.parser := ⟨[]⟩
instance quoted_symbol.view : parser.has_view quoted_symbol.parser syntax := default _

@[derive parser.has_tokens parser.has_view]
def symbol_quote.parser : term_parser :=
node! notation_quoted_symbol [
  left_quote: raw $ ch '`',
  symbol: quoted_symbol.parser,
  right_quote: raw (ch '`') tt, -- consume trailing ws
  prec: precedence.parser?]

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive parser.has_tokens parser.has_view]
def notation_symbol.parser : term_parser :=
node_choice! notation_symbol {
  quoted: symbol_quote.parser
  --TODO, {read := do tk ← token, /- check if reserved token-/}
}

@[derive parser.has_tokens parser.has_view]
def action.parser : term_parser :=
node! action [":", action: node_choice! action_kind {
  prec: number,
  max: symbol_or_ident "max",
  prev: symbol_or_ident "prev",
  scoped: symbol_or_ident "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/}]

@[derive parser.has_tokens parser.has_view]
def transition.parser : term_parser :=
node_choice! transition {
  binder: node! binder ["binder", prec: precedence.parser?],
  binders: node! binders ["binders", prec: precedence.parser?],
  arg: node! argument [id: ident.parser, action: action.parser?]
}

@[derive parser.has_tokens parser.has_view]
def rule.parser : term_parser :=
node! rule [symbol: notation_symbol.parser, transition: transition.parser?]

end notation_spec

@[derive parser.has_tokens parser.has_view]
def notation_spec.parser : term_parser :=
node_choice! notation_spec {
  number_literal: number,
  rules: node! notation_spec.rules [id: ident.parser?, rules: notation_spec.rule.parser*]
}

@[derive parser.has_tokens parser.has_view]
def notation.parser : term_parser :=
node! «notation» ["notation", spec: notation_spec.parser, ":=", term: recurse 0]

@[derive parser.has_tokens parser.has_view]
def reserve_notation.parser : term_parser :=
node! «reserve_notation» [try ["reserve", "notation"], spec: notation_spec.parser]

@[derive parser.has_tokens parser.has_view]
def mixfix.kind.parser : term_parser :=
node_choice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive parser.has_tokens parser.has_view]
def mixfix.parser : term_parser :=
node! «mixfix» [
  kind: mixfix.kind.parser,
  symbol: notation_spec.notation_symbol.parser, ":=", term: recurse 0]

@[derive parser.has_tokens parser.has_view]
def reserve_mixfix.parser : term_parser :=
node! «reserve_mixfix» [
  try ["reserve", kind: mixfix.kind.parser],
  symbol: notation_spec.notation_symbol.parser]

end «command»
end parser
end lean
