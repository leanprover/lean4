/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Ullrich

Command parsers
-/
prelude
import init.lean.parser.declaration

namespace lean
namespace parser

open combinators monad_parsec
open parser.has_tokens parser.has_view

local postfix `?`:10000 := optional
local postfix *:10000 := combinators.many
local postfix +:10000 := combinators.many1

set_option class.instance_max_depth 300

@[derive parser.has_view parser.has_tokens]
def command.parser : command_parser :=
recurse () <?> "command"

namespace «command»

@[derive parser.has_view parser.has_tokens]
def open_spec.parser : command_parser :=
node! open_spec [
 id: ident.parser,
 as: node! open_spec.as ["as", id: ident.parser]?,
 only: node! open_spec.only [try ["(", id: ident.parser], ids: ident.parser*, ")"]?,
 «renaming»: node! open_spec.renaming [try ["(", "renaming"], items: node! open_spec.renaming.item [«from»: ident.parser, "->", to: ident.parser]+, ")"]?,
 «hiding»: node! open_spec.hiding ["(", "hiding", ids: ident.parser+, ")"]?
]+

@[derive parser.has_tokens]
def open.parser : command_parser :=
node! «open» ["open", spec: open_spec.parser]

@[derive parser.has_tokens]
def export.parser : command_parser :=
node! «export» ["export", spec: open_spec.parser]

@[derive parser.has_tokens]
def section.parser : command_parser :=
node! «section» ["section", name: ident.parser?]

@[derive parser.has_tokens]
def namespace.parser : command_parser :=
node! «namespace» ["namespace", name: ident.parser]

@[derive parser.has_tokens]
def variable.parser : command_parser :=
node! «variable» ["variable", binder: term.binder.parser]

@[derive parser.has_tokens]
def variables.parser : command_parser :=
-- TODO: should require at least one binder
node! «variables» ["variables", binders: term.bracketed_binders.parser]

@[derive parser.has_tokens]
def include.parser : command_parser :=
node! «include» ["include ", ids: ident.parser+]

@[derive parser.has_tokens]
def omit.parser : command_parser :=
node! «omit» ["omit ", ids: ident.parser+]

@[derive parser.has_tokens]
def end.parser : command_parser :=
node! «end» ["end", name: ident.parser?]

@[derive parser.has_tokens]
def universe.parser : command_parser :=
any_of [
  node! «universes» ["universes", ids: ident.parser+],
  node! «universe» ["universe", id: ident.parser]
]

@[derive parser.has_tokens parser.has_view]
def check.parser : command_parser :=
node! check ["#check", term: term.parser]

@[derive parser.has_tokens parser.has_view]
def attribute.parser : command_parser :=
node! «attribute» [
  try [«local»: (symbol "local ")?, "attribute "],
  "[",
  attrs: sep_by1 attr_instance.parser (symbol ", "),
  "] ",
  ids: ident.parser*
]

@[derive parser.has_tokens parser.has_view]
def init_quot.parser : command_parser :=
node! «init_quot» ["init_quot"]

@[derive parser.has_tokens parser.has_view]
def set_option.parser : command_parser :=
node! «set_option» ["set_option", opt: ident.parser, val: node_choice! option_value {
  bool: node_choice! bool_option_value {
    true: symbol_or_ident "true",
    false: symbol_or_ident "true",
  },
  string: string_lit.parser,
  -- TODO(Sebastian): fractional numbers
  num: number.parser,
}]

@[derive has_tokens]
def builtin_command_parsers : token_map command_parser := token_map.of_list [
  ("/--", declaration.parser),
  ("@[", declaration.parser),
  ("private", declaration.parser),
  ("protected", declaration.parser),
  ("noncomputable", declaration.parser),
  ("unsafe", declaration.parser),
  ("def", declaration.parser),
  ("abbreviation", declaration.parser),
  ("abbrev", declaration.parser),
  ("theorem", declaration.parser),
  ("instance", declaration.parser),
  ("axiom", declaration.parser),
  ("constant", declaration.parser),
  ("class", declaration.parser),
  ("inductive", declaration.parser),
  ("structure", declaration.parser),

  ("variable", variable.parser),
  ("variables", variables.parser),
  ("namespace", namespace.parser),
  ("end", end.parser),
  ("open", open.parser),
  ("section", section.parser),
  ("universe", universe.parser),
  ("universes", universe.parser),
  ("local", notation.parser),
  ("notation", notation.parser),
  ("reserve", reserve_notation.parser),
  ("local", mixfix.parser),
  ("prefix", mixfix.parser),
  ("infix", mixfix.parser),
  ("infixl", mixfix.parser),
  ("infixr", mixfix.parser),
  ("postfix", mixfix.parser),
  ("reserve", reserve_mixfix.parser),
  ("#check", check.parser),
  ("local", attribute.parser),
  ("attribute", attribute.parser),
  ("export", export.parser),
  ("include", include.parser),
  ("omit", omit.parser),
  ("init_quot", init_quot.parser),
  ("set_option", set_option.parser)]
end «command»

def command_parser.run (commands : token_map command_parser) (p : command_parser)
  : parser_t command_parser_config id syntax :=
λ cfg, (p.run cfg).run_parsec $ λ _, (indexed commands >>= any_of : command_parser).run cfg

end parser
end lean
