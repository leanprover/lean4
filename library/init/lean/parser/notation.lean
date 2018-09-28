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
def precedence.parser : term_parser :=
node! «precedence» [":", prec: number.parser]/-TODO <|> expr-/

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

def unquoted_symbol.parser : term_parser :=
try $ do {
  it ← left_over,
  stx@(syntax.atom _) ← monad_lift token | error "" (dlist.singleton "symbol") it,
  pure stx
} <?> "symbol"

instance unquoted_symbol.tokens : parser.has_tokens unquoted_symbol.parser := ⟨[]⟩
instance unquoted_symbol.view : parser.has_view unquoted_symbol.parser syntax := default _

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
def action.parser : term_parser :=
node! action [":", action: node_choice! action_kind {
  prec: number.parser,
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
node! notation_spec [prefix_arg: ident.parser?, rules: notation_spec.rule.parser*]

@[derive parser.has_tokens parser.has_view]
def notation.parser : term_parser :=
node! «notation» ["notation", spec: notation_spec.parser, ":=", term: term.parser]

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
open «command»
open command.notation_spec

def command_parser_config.register_notation_tokens (spec : notation_spec.view) (cfg : command_parser_config) :
  except string command_parser_config :=
do spec.rules.mfoldl (λ (cfg : command_parser_config) r, match r.symbol with
   | notation_symbol.view.quoted {symbol := syntax.atom a, prec := some prec, ..} :=
     pure {cfg with tokens := cfg.tokens.insert a.val {«prefix» := a.val}}
   | _ := throw "register_notation: unreachable") cfg

def command_parser_config.register_notation_parser (spec : notation_spec.view) (cfg : command_parser_config) :
  except string command_parser_config :=
do -- build and register parser
   let k : syntax_node_kind := {name := "notation<TODO>"},
   ps ← spec.rules.mmap (λ r : rule.view, do
     psym ← match r.symbol with
     | notation_symbol.view.quoted {symbol := syntax.atom a ..} :=
       pure (symbol a.val : term_parser)
     | _ := throw "register_notation: unreachable",
     ptrans ← match r.transition with
     | some (transition.view.arg arg) := pure $ some term.parser
     | none := pure $ none
     | _ := throw "register_notation: unimplemented",
     pure $ psym::ptrans.to_monad
   ),
   let ps := ps.bind id,
   cfg ← match spec.prefix_arg with
   | none   := pure {cfg with leading_term_parsers := node k ps::cfg.leading_term_parsers}
   | some _ := pure {cfg with trailing_term_parsers := node k (read::ps.map coe)::cfg.trailing_term_parsers},
   pure cfg

end parser
end lean
