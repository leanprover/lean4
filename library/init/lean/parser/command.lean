/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Command parsers
-/
prelude
import init.lean.parser.term

namespace lean
namespace parser
open combinators monad_parsec
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

@[derive parser.has_view parser.has_tokens]
def command_parser.recurse : command_parser := recurse ()

set_option class.instance_max_depth 200
@[derive parser.has_view parser.has_tokens]
def open_spec.parser : command_parser :=
node! open_spec [
 id: ident,
 as: node! open_spec.as ["as", id: ident]?,
 only: node! open_spec.only [try ["(", id: ident], ids: ident*, ")"]?,
 «renaming»: node! open_spec.renaming [try ["(", "renaming"], items: node! open_spec.renaming.item [«from»: ident, "->", to: ident]+, ")"]?,
 «hiding»: node! open_spec.hiding ["(", "hiding", ids: ident+, ")"]?
]+

@[derive parser.has_tokens]
def open.parser : command_parser :=
node! «open» ["open", spec: open_spec.parser]

@[derive parser.has_tokens]
def section.parser : command_parser :=
node! «section» ["section", name: ident?, commands: command_parser.recurse*, "end", end_name: ident?]

@[derive parser.has_tokens]
def universe.parser : command_parser :=
any_of [
  -- local
  node! universe_variables [try ["universe", "variables"], ids: ident+],
  -- global
  node! «universes» ["universes", ids: ident+],
  node! «universe» ["universe", id: ident]
]

namespace notation_spec
@[derive parser.has_tokens parser.has_view]
def precedence.parser : command_parser :=
node! «precedence» [":", prec: number]/-TODO <|> expr-/

def quoted_symbol.parser : command_parser :=
do (s, info) ← with_source_info $ take_until (= '`'),
   pure $ syntax.atom ⟨info, atomic_val.string s⟩

instance quoted_symbol.tokens : parser.has_tokens quoted_symbol.parser := ⟨[]⟩
instance quoted_symbol.view : parser.has_view quoted_symbol.parser syntax := default _

@[derive parser.has_tokens parser.has_view]
def symbol_quote.parser : command_parser :=
node! notation_quoted_symbol [
  left_quote: raw_symbol "`",
  symbol: quoted_symbol.parser,
  right_quote: raw_symbol "`",
  prec: precedence.parser?]

--TODO(Sebastian): cannot be called `symbol` because of hygiene problems
@[derive parser.has_tokens parser.has_view]
def notation_symbol.parser : command_parser :=
node_choice! notation_symbol {
  quoted: symbol_quote.parser
  --TODO, {read := do tk ← token, /- check if reserved token-/}
}

@[derive parser.has_tokens parser.has_view]
def action.parser : command_parser :=
node! action [":", action: node_choice! action_kind {
  prec: number,
  max: raw_symbol "max",
  prev: raw_symbol "prev",
  scoped: raw_symbol "scoped"
  /-TODO seq [
    "(",
    any_of ["foldl", "foldr"],
    optional prec,
    notation_tk,-/}]

@[derive parser.has_tokens parser.has_view]
def transition.parser : command_parser :=
node_choice! transition {
  binder: node! binder ["binder", prec: precedence.parser?],
  binders: node! binders ["binders", prec: precedence.parser?],
  arg: node! argument [id: ident, action: action.parser?]
}

@[derive parser.has_tokens parser.has_view]
def rule.parser : command_parser :=
node! rule [symbol: notation_symbol.parser, transition: transition.parser?]

end notation_spec

@[derive parser.has_tokens parser.has_view]
def notation_spec.parser : command_parser :=
node_choice! notation_spec {
  number_literal: number,
  rules: node! notation_spec.rules [id: ident?, rules: notation_spec.rule.parser*]
}

@[derive parser.has_tokens parser.has_view]
def notation.parser : command_parser :=
node! «notation» ["notation", spec: notation_spec.parser, ":=", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def reserve_notation.parser : command_parser :=
node! «reserve_notation» [try ["reserve", "notation"], spec: notation_spec.parser]

@[derive parser.has_tokens parser.has_view]
def mixfix.kind.parser : command_parser :=
node_choice! mixfix.kind {"prefix", "infix", "infixl", "infixr", "postfix"}

@[derive parser.has_tokens parser.has_view]
def mixfix.parser : command_parser :=
node! «mixfix» [
  kind: mixfix.kind.parser,
  symbol: notation_spec.notation_symbol.parser, ":=", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def reserve_mixfix.parser : command_parser :=
node! «reserve_mixfix» [
  try ["reserve", kind: mixfix.kind.parser],
  symbol: notation_spec.notation_symbol.parser]

@[derive parser.has_tokens parser.has_view]
def check.parser : command_parser :=
node! check ["#check", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def command.parser : command_parser :=
any_of [open.parser, section.parser, universe.parser, notation.parser, reserve_notation.parser,
  mixfix.parser, reserve_mixfix.parser, check.parser] <?> "command"

end parser

namespace parser
open syntax_node_kind.has_view combinators notation_spec

-- example macro
def mixfix.expand (stx : syntax) : option syntax :=
do v ← view mixfix stx,
   -- TODO: reserved token case
   notation_symbol.view.quoted {prec:=prec, ..} ← pure v.symbol,
   -- `notation` allows more syntax after `:` than mixfix commands, so we have to do a small conversion
   let prec_to_action : precedence.view → action.view :=
     λ prec, {action := action_kind.view.prec prec.prec, ..prec},
   let spec := view.rules $ match v.kind with
     | mixfix.kind.view.prefix _ := {
       id := optional_view.none,
       rules := [{
         symbol := v.symbol,
         transition := optional_view.some $ transition.view.arg $ {
           id := `b,
           action := prec_to_action <$> prec}}]}
     | _ := sorry,
   pure $ review «notation» ⟨"notation", spec, ":=", v.term⟩

end parser
end lean
