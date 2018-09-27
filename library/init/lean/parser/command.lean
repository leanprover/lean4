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
def section.parser : command_parser :=
node! «section» ["section", name: ident.parser?, commands: command.parser*, "end", end_name: ident.parser?]

@[derive parser.has_tokens]
def universe.parser : command_parser :=
any_of [
  -- local
  node! universe_variables [try ["universe", "variables"], ids: ident.parser+],
  -- global
  node! «universes» ["universes", ids: ident.parser+],
  node! «universe» ["universe", id: ident.parser]
]

@[derive parser.has_tokens parser.has_view]
def check.parser : command_parser :=
node! check ["#check", term: term.parser]

@[derive has_tokens]
def builtin_command_parsers : list command_parser := [
  open.parser, section.parser, universe.parser, notation.parser, reserve_notation.parser,
  mixfix.parser, reserve_mixfix.parser, check.parser, declaration.parser]
end «command»

def command_parser.run (commands : list command_parser) (p : command_parser)
  : parser_t command_parser_config id syntax :=
λ cfg, (p.run cfg).run_parsec $ λ _, any_of $ commands.map (λ p, p.run cfg)

end parser
end lean
